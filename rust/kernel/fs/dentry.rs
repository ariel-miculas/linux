// SPDX-License-Identifier: GPL-2.0

//! File system directory entries.
//!
//! This module allows Rust code to use dentries.
//!
//! C headers: [`include/linux/dcache.h`](srctree/include/linux/dcache.h)

use super::{inode::INode, FileSystem, SuperBlock};
use crate::bindings;
use crate::error::{code::*, from_err_ptr, Result};
use crate::types::{ARef, AlwaysRefCounted, Opaque};
use core::{marker::PhantomData, mem::ManuallyDrop, ops::Deref, ptr};

/// A directory entry.
///
/// Wraps the kernel's `struct dentry`.
///
/// # Invariants
///
/// Instances of this type are always ref-counted, that is, a call to `dget` ensures that the
/// allocation remains valid at least until the matching call to `dput`.
#[repr(transparent)]
pub struct DEntry<T: FileSystem + ?Sized>(pub(crate) Opaque<bindings::dentry>, PhantomData<T>);

// SAFETY: The type invariants guarantee that `DEntry` is always ref-counted.
unsafe impl<T: FileSystem + ?Sized> AlwaysRefCounted for DEntry<T> {
    fn inc_ref(&self) {
        // SAFETY: The existence of a shared reference means that the refcount is nonzero.
        unsafe { bindings::dget(self.0.get()) };
    }

    unsafe fn dec_ref(obj: ptr::NonNull<Self>) {
        // SAFETY: The safety requirements guarantee that the refcount is nonzero.
        unsafe { bindings::dput(obj.as_ref().0.get()) }
    }
}

impl<T: FileSystem + ?Sized> DEntry<T> {
    /// Creates a new [`DEntry`] from a raw C pointer.
    ///
    /// # Safety
    ///
    /// * `ptr` must be valid for at least the lifetime of the returned reference.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    #[allow(dead_code)]
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::dentry) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the reference is and remains valid.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Returns the superblock of the dentry.
    pub fn super_block(&self) -> &SuperBlock<T> {
        // `d_sb` is immutable, so it's safe to read it.
        unsafe { SuperBlock::from_raw((*self.0.get()).d_sb) }
    }
}

/// A dentry that is known to be unhashed.
pub struct Unhashed<'a, T: FileSystem + ?Sized>(pub(crate) &'a DEntry<T>);

impl<T: FileSystem + ?Sized> Unhashed<'_, T> {
    /// Splices a disconnected dentry into the tree if one exists.
    pub fn splice_alias(self, inode: Option<ARef<INode<T>>>) -> Result<Option<ARef<DEntry<T>>>> {
        let inode_ptr = if let Some(i) = inode {
            // Reject inode if it belongs to a different superblock.
            if !ptr::eq(i.super_block(), self.0.super_block()) {
                return Err(EINVAL);
            }

            ManuallyDrop::new(i).0.get()
        } else {
            ptr::null_mut()
        };

        // SAFETY: Both inode and dentry are known to be valid.
        let ptr = from_err_ptr(unsafe { bindings::d_splice_alias(inode_ptr, self.0 .0.get()) })?;

        // SAFETY: The C API guarantees that if a dentry is returned, the refcount has been
        // incremented.
        Ok(ptr::NonNull::new(ptr).map(|v| unsafe { ARef::from_raw(v.cast::<DEntry<T>>()) }))
    }

    /// Returns the name of the dentry.
    ///
    /// Being unhashed guarantees that the name won't change.
    pub fn name(&self) -> &[u8] {
        // SAFETY: The name is immutable, so it is ok to read it.
        let name = unsafe { &*ptr::addr_of!((*self.0 .0.get()).d_name) };

        // This ensures that a `u32` is representable in `usize`. If it isn't, we'll get a build
        // break.
        const _: usize = 0xffffffff;

        // SAFETY: The union is just allow an easy way to get the `hash` and `len` at once. `len`
        // is always valid.
        let len = unsafe { name.__bindgen_anon_1.__bindgen_anon_1.len } as usize;

        // SAFETY: The name is immutable, so it is ok to read it.
        unsafe { core::slice::from_raw_parts(name.name, len) }
    }
}

impl<T: FileSystem + ?Sized> Deref for Unhashed<'_, T> {
    type Target = DEntry<T>;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

/// A dentry that is meant to be used as the root of a file system.
pub struct Root<T: FileSystem + ?Sized>(ARef<DEntry<T>>);

impl<T: FileSystem + ?Sized> Root<T> {
    /// Creates a root dentry.
    pub fn try_new(inode: ARef<INode<T>>) -> Result<Root<T>> {
        // SAFETY: `d_make_root` requires that `inode` be valid and referenced, which is the
        // case for this call.
        //
        // It takes over the inode, even on failure, so we don't need to clean it up.
        let dentry_ptr = unsafe { bindings::d_make_root(ManuallyDrop::new(inode).0.get()) };
        let dentry = ptr::NonNull::new(dentry_ptr).ok_or(ENOMEM)?;

        // SAFETY: `dentry` is valid and referenced. It reference ownership is transferred to
        // `ARef`.
        Ok(Root(unsafe { ARef::from_raw(dentry.cast::<DEntry<T>>()) }))
    }
}

impl<T: FileSystem + ?Sized> Deref for Root<T> {
    type Target = DEntry<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

// SPDX-License-Identifier: GPL-2.0

//! File system super blocks.
//!
//! This module allows Rust code to use superblocks.
//!
//! C headers: [`include/linux/fs.h`](srctree/include/linux/fs.h)

use super::inode::{self, INode, Ino};
use super::FileSystem;
use crate::bindings;
use crate::error::{code::*, Result};
use crate::types::{ARef, Either, Opaque};
use core::{marker::PhantomData, ptr};

/// A file system super block.
///
/// Wraps the kernel's `struct super_block`.
#[repr(transparent)]
pub struct SuperBlock<T: FileSystem + ?Sized>(
    pub(crate) Opaque<bindings::super_block>,
    PhantomData<T>,
);

impl<T: FileSystem + ?Sized> SuperBlock<T> {
    /// Creates a new superblock reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::super_block) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }

    /// Creates a new superblock mutable reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that:
    ///
    /// * `ptr` is valid and remains so for the lifetime of the returned object.
    /// * `ptr` has the correct file system type, or `T` is [`super::UnspecifiedFS`].
    /// * `ptr` is the only active pointer to the superblock.
    pub(crate) unsafe fn from_raw_mut<'a>(ptr: *mut bindings::super_block) -> &'a mut Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &mut *ptr.cast::<Self>() }
    }

    /// Returns whether the superblock is mounted in read-only mode.
    pub fn rdonly(&self) -> bool {
        // SAFETY: `s_flags` only changes during init, so it is safe to read it.
        unsafe { (*self.0.get()).s_flags & bindings::SB_RDONLY != 0 }
    }

    /// Sets the magic number of the superblock.
    pub fn set_magic(&mut self, magic: usize) -> &mut Self {
        // SAFETY: This is a new superblock that is being initialised, so it's ok to write to its
        // fields.
        unsafe { (*self.0.get()).s_magic = magic as core::ffi::c_ulong };
        self
    }

    /// Tries to get an existing inode or create a new one if it doesn't exist yet.
    pub fn get_or_create_inode(&self, ino: Ino) -> Result<Either<ARef<INode<T>>, inode::New<T>>> {
        // SAFETY: All superblock-related state needed by `iget_locked` is initialised by C code
        // before calling `fill_super_callback`, or by `fill_super_callback` itself before calling
        // `super_params`, which is the first function to see a new superblock.
        let inode =
            ptr::NonNull::new(unsafe { bindings::iget_locked(self.0.get(), ino) }).ok_or(ENOMEM)?;

        // SAFETY: `inode` is a valid pointer returned by `iget_locked`.
        unsafe { bindings::spin_lock(ptr::addr_of_mut!((*inode.as_ptr()).i_lock)) };

        // SAFETY: `inode` is valid and was locked by the previous lock.
        let state = unsafe { *ptr::addr_of!((*inode.as_ptr()).i_state) };

        // SAFETY: `inode` is a valid pointer returned by `iget_locked`.
        unsafe { bindings::spin_unlock(ptr::addr_of_mut!((*inode.as_ptr()).i_lock)) };

        if state & u64::from(bindings::I_NEW) == 0 {
            // The inode is cached. Just return it.
            //
            // SAFETY: `inode` had its refcount incremented by `iget_locked`; this increment is now
            // owned by `ARef`.
            Ok(Either::Left(unsafe { ARef::from_raw(inode.cast()) }))
        } else {
            // SAFETY: The new inode is valid but not fully initialised yet, so it's ok to create a
            // `inode::New`.
            Ok(Either::Right(inode::New(inode, PhantomData)))
        }
    }

    /// Creates an inode with the given inode number.
    ///
    /// Fails with `EEXIST` if an inode with the given number already exists.
    pub fn create_inode(&self, ino: Ino) -> Result<inode::New<T>> {
        if let Either::Right(new) = self.get_or_create_inode(ino)? {
            Ok(new)
        } else {
            Err(EEXIST)
        }
    }
}

//! Mount interface
//!
//! C headers: [`include/linux/mount.h`](../../../../include/linux/mount.h)

use kernel::bindings;
use kernel::error::from_err_ptr;
use kernel::pr_err;
use kernel::prelude::*;
use kernel::str::CStr;
use kernel::types::Opaque;

/// Wraps the kernel's `struct path`.
#[repr(transparent)]
pub struct Path(pub(crate) Opaque<bindings::path>);

/// Wraps the kernel's `struct vfsmount`.
#[repr(transparent)]
#[derive(Debug)]
pub struct Vfsmount {
    vfsmount: *mut bindings::vfsmount,
}

// SAFETY: No one besides us has the raw pointer, so we can safely transfer Vfsmount to another thread
unsafe impl Send for Vfsmount {}
// SAFETY: It's OK to access `Vfsmount` through references from other threads because we're not
// accessing any properties from the underlying raw pointer
unsafe impl Sync for Vfsmount {}

impl Vfsmount {
    /// Create a new private mount clone based on a path name
    pub fn new_private_mount(path_name: &CStr) -> Result<Self> {
        let path: Path = Path(Opaque::uninit());
        let err = unsafe {
            bindings::kern_path(
                path_name.as_ptr() as *const i8,
                bindings::LOOKUP_FOLLOW | bindings::LOOKUP_DIRECTORY,
                path.0.get(),
            )
        };
        if err != 0 {
            pr_err!("failed to resolve '{}': {}\n", path_name, err);
            return Err(EINVAL);
        }

        let vfsmount = unsafe {
            let mnt = from_err_ptr(bindings::clone_private_mount(path.0.get()))?;
            // Don't inherit atime flags
            (*mnt).mnt_flags &=
                !(bindings::MNT_NOATIME | bindings::MNT_NODIRATIME | bindings::MNT_RELATIME) as i32;
            mnt
        };
        Ok(Self { vfsmount })
    }

    /// Returns a raw pointer to vfsmount
    pub fn get(&self) -> *mut bindings::vfsmount {
        self.vfsmount
    }
}

impl Drop for Vfsmount {
    fn drop(&mut self) {
        // SAFETY new_private_mount makes sure to return a valid pointer
        unsafe { bindings::kern_unmount(self.vfsmount) };
    }
}

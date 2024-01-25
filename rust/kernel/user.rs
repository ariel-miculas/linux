// SPDX-License-Identifier: GPL-2.0

//! User-space related functions.

use crate::error::{code::*, Result};

/// A writer to userspace memory.
pub struct Writer {
    ptr: *mut u8,
    len: usize,
}

impl Writer {
    pub(crate) fn new(ptr: *mut i8, len: usize) -> Self {
        Self {
            ptr: ptr.cast::<u8>(),
            len,
        }
    }

    /// Writes all of `data` into user memory.
    pub fn write_all(&mut self, data: &[u8]) -> Result {
        let len = data.len();
        if len > self.len {
            return Err(EFAULT);
        }

        let pending = unsafe {
            bindings::copy_to_user(
                self.ptr.cast::<core::ffi::c_void>(),
                data.as_ptr().cast::<core::ffi::c_void>(),
                data.len().try_into()?,
            )
        };
        if pending != 0 {
            return Err(EFAULT);
        }

        self.ptr = self.ptr.wrapping_add(len);
        self.len -= len;

        Ok(())
    }
}

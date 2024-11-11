// SPDX-License-Identifier: GPL-2.0

//! Types for working with the block layer.

pub mod mq;

/// Block devices.
///
/// This module allows Rust code to use block devices.
///
/// C headers: [`include/linux/blk_types.h`](../../include/linux/blk_types.h)

use crate::bindings;
use crate::types::Opaque;

/// The type used for indexing onto a disc or disc partition.
///
/// This is C's `sector_t`.
pub type Sector = u64;

/// The type of the inode's block count.
///
/// This is C's `blkcnt_t`.
pub type Count = u64;

/// A block device.
///
/// Wraps the kernel's `struct block_device`.
#[repr(transparent)]
pub struct Device(pub(crate) Opaque<bindings::block_device>);

impl Device {
    /// Creates a new block device reference from the given raw pointer.
    ///
    /// # Safety
    ///
    /// Callers must ensure that `ptr` is valid and remains so for the lifetime of the returned
    /// object.
    pub(crate) unsafe fn from_raw<'a>(ptr: *mut bindings::block_device) -> &'a Self {
        // SAFETY: The safety requirements guarantee that the cast below is ok.
        unsafe { &*ptr.cast::<Self>() }
    }
}

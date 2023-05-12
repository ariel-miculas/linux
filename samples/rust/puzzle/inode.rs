// This contents of this file is taken from puzzlefs.rs (the userspace implementation)
// It is named inode.rs instead puzzlefs.rs since the root of this kernel module already has that name

use crate::puzzle::error::Result;
use crate::puzzle::error::WireFormatError;
use crate::puzzle::types as format;
use crate::puzzle::types::{Inode, InodeMode, MetadataBlob};
use alloc::vec::Vec;
use kernel::prelude::ENOENT;

pub(crate) struct PuzzleFS {
    layers: Vec<format::MetadataBlob>,
}

impl PuzzleFS {
    pub(crate) fn new(md: MetadataBlob) -> Result<Self> {
        let mut v = Vec::new();
        v.try_push(md)?;
        Ok(PuzzleFS { layers: v })
    }

    pub(crate) fn find_inode(&self, ino: u64) -> Result<Inode> {
        for layer in self.layers.iter() {
            if let Some(inode) = layer.find_inode(ino)? {
                let inode = Inode::from_capnp(inode)?;
                if let InodeMode::Wht = inode.mode {
                    // TODO: seems like this should really be an Option.
                    return Err(WireFormatError::from_errno(ENOENT));
                }
                return Ok(inode);
            }
        }

        Err(WireFormatError::from_errno(ENOENT))
    }
}

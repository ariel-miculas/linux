// This contents of this file is taken from puzzlefs.rs (the userspace implementation)
// It is named inode.rs instead puzzlefs.rs since the root of this kernel module already has that name

use crate::puzzle::error::Result;
use crate::puzzle::error::WireFormatError;
use crate::puzzle::oci::Image;
use crate::puzzle::types as format;
use crate::puzzle::types::{Digest, Inode, InodeMode};
use alloc::vec::Vec;
use kernel::mount::Vfsmount;
use kernel::prelude::ENOENT;
use kernel::str::CStr;

pub(crate) struct PuzzleFS {
    pub(crate) oci: Image,
    layers: Vec<format::MetadataBlob>,
}

impl PuzzleFS {
    pub(crate) fn open(oci_root_dir: &CStr, rootfs_path: &CStr) -> Result<PuzzleFS> {
        let vfs_mount = Vfsmount::new_private_mount(oci_root_dir)?;
        let oci = Image::open(vfs_mount)?;
        let rootfs = oci.open_rootfs_blob(rootfs_path)?;

        let mut layers = Vec::new();
        for md in rootfs.metadatas.iter() {
            let digest = Digest::try_from(md)?;
            layers.try_push(oci.open_metadata_blob(&digest)?)?;
        }

        Ok(PuzzleFS { oci, layers })
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

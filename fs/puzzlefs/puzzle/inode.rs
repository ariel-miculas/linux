// This contents of this file is taken from puzzlefs.rs (the userspace implementation)
// It is named inode.rs instead puzzlefs.rs since the root of this kernel module already has that name

use crate::puzzle::error::Result;
use crate::puzzle::error::WireFormatError;
use crate::puzzle::oci::Image;
use crate::puzzle::types as format;
use crate::puzzle::types::{Digest, Inode, InodeMode};
use alloc::vec::Vec;
use kernel::mount::Vfsmount;
use kernel::prelude::{ENOENT, ENOTDIR};
use kernel::str::CStr;

pub(crate) struct PuzzleFS {
    pub(crate) oci: Image,
    layers: Vec<format::MetadataBlob>,
    pub(crate) total_inodes: u64,
    pub(crate) total_block_size: u64,
}

impl PuzzleFS {
    pub(crate) fn open(oci_root_dir: &CStr, rootfs_path: &CStr) -> Result<PuzzleFS> {
        let vfs_mount = Vfsmount::new_private_mount(oci_root_dir)?;
        let oci = Image::open(vfs_mount)?;
        let rootfs = oci.open_rootfs_blob(rootfs_path)?;

        let mut total_block_size = 0;
        let mut total_inodes: u64 = 0;
        let mut layers = Vec::new();
        for md in rootfs.metadatas.iter() {
            let digest = Digest::try_from(md)?;
            let layer = oci.open_metadata_blob(&digest)?;

            // This may take up too much time, but we need to implement statfs if we want to use
            // puzzlefs as a lower filesystem in overlayfs
            let inodes = layer.get_inode_vector()?;
            total_inodes += u64::from(inodes.len());
            for inode_number in 0..inodes.len() {
                let inode = Inode::from_capnp(inodes.get(inode_number))?;
                if let InodeMode::File { chunks } = inode.mode {
                    total_block_size += chunks.iter().map(|chunk| chunk.len).sum::<u64>();
                }
            }

            layers.try_push(layer)?;
        }

        Ok(PuzzleFS {
            oci,
            layers,
            total_inodes,
            total_block_size,
        })
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

pub(crate) fn file_read(
    oci: &Image,
    inode: &Inode,
    offset: usize,
    data: &mut [u8],
) -> Result<usize> {
    let chunks = match &inode.mode {
        InodeMode::File { chunks } => chunks,
        _ => return Err(WireFormatError::from_errno(ENOTDIR)),
    };

    // TODO: fix all this casting...
    let end = offset + data.len();

    let mut file_offset = 0;
    let mut buf_offset = 0;
    for chunk in chunks {
        // have we read enough?
        if file_offset > end {
            break;
        }

        // should we skip this chunk?
        if file_offset + (chunk.len as usize) < offset {
            file_offset += chunk.len as usize;
            continue;
        }

        let addl_offset = if offset > file_offset {
            offset - file_offset
        } else {
            0
        };

        // ok, need to read this chunk; how much?
        let left_in_buf = data.len() - buf_offset;
        let to_read = core::cmp::min(left_in_buf, chunk.len as usize - addl_offset);

        let start = buf_offset;
        let finish = start + to_read;
        file_offset += addl_offset;

        // how many did we actually read?
        let n = oci.fill_from_chunk(chunk.blob, addl_offset as u64, &mut data[start..finish])?;
        file_offset += n;
        buf_offset += n;
    }

    // discard any extra if we hit EOF
    Ok(buf_offset)
}

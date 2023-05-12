use crate::puzzle::error::Result;
use crate::puzzle::error::WireFormatError;
use alloc::vec::Vec;
use capnp::{message, serialize};
use core::fmt;
use hex::{encode_hex_iter, FromHexError};
use kernel::file;
use kernel::str::CStr;

pub(crate) mod manifest_capnp;
pub(crate) mod metadata_capnp;

pub(crate) const SHA256_BLOCK_SIZE: usize = 32;

#[derive(Debug)]
pub(crate) struct Rootfs {
    pub(crate) metadatas: Vec<BlobRef>,
    #[allow(dead_code)]
    pub(crate) manifest_version: u64,
}

impl Rootfs {
    pub(crate) fn open(file: file::RegularFile) -> Result<Rootfs> {
        let manifest_buffer = file.read_to_end()?;
        let message_reader = serialize::read_message_from_flat_slice_no_alloc(
            &mut &manifest_buffer[..],
            ::capnp::message::ReaderOptions::new(),
        )?;
        let rootfs = message_reader.get_root::<crate::manifest_capnp::rootfs::Reader<'_>>()?;
        Self::from_capnp(rootfs)
    }

    pub(crate) fn from_capnp(reader: crate::manifest_capnp::rootfs::Reader<'_>) -> Result<Self> {
        let metadatas = reader.get_metadatas()?;

        let mut metadata_vec = Vec::new();
        for blobref in metadatas.iter() {
            metadata_vec.try_push(BlobRef::from_capnp(blobref)?)?;
        }

        Ok(Rootfs {
            metadatas: metadata_vec,
            manifest_version: reader.get_manifest_version(),
        })
    }
}

// TODO: should this be an ociv1 digest and include size and media type?
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BlobRef {
    pub(crate) digest: [u8; SHA256_BLOCK_SIZE],
    pub(crate) offset: u64,
    pub(crate) compressed: bool,
}

impl BlobRef {
    pub(crate) fn from_capnp(reader: metadata_capnp::blob_ref::Reader<'_>) -> Result<Self> {
        let digest = reader.get_digest()?;
        Ok(BlobRef {
            digest: digest.try_into()?,
            offset: reader.get_offset(),
            compressed: reader.get_compressed(),
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct DirEnt {
    pub(crate) ino: Ino,
    pub(crate) name: Vec<u8>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct DirList {
    // TODO: flags instead?
    pub(crate) look_below: bool,
    pub(crate) entries: Vec<DirEnt>,
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct FileChunk {
    pub(crate) blob: BlobRef,
    pub(crate) len: u64,
}

pub(crate) type Ino = u64;

impl FileChunk {
    pub(crate) fn from_capnp(reader: metadata_capnp::file_chunk::Reader<'_>) -> Result<Self> {
        let len = reader.get_len();
        let blob = BlobRef::from_capnp(reader.get_blob()?)?;

        Ok(FileChunk { blob, len })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Inode {
    pub(crate) ino: Ino,
    pub(crate) mode: InodeMode,
    pub(crate) uid: u32,
    pub(crate) gid: u32,
    pub(crate) permissions: u16,
    pub(crate) additional: Option<InodeAdditional>,
}

impl Inode {
    pub(crate) fn from_capnp(reader: metadata_capnp::inode::Reader<'_>) -> Result<Self> {
        Ok(Inode {
            ino: reader.get_ino(),
            mode: InodeMode::from_capnp(reader.get_mode())?,
            uid: reader.get_uid(),
            gid: reader.get_gid(),
            permissions: reader.get_permissions(),
            additional: InodeAdditional::from_capnp(reader.get_additional()?)?,
        })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) enum InodeMode {
    Unknown,
    Fifo,
    Chr { major: u64, minor: u64 },
    Dir { dir_list: DirList },
    Blk { major: u64, minor: u64 },
    File { chunks: Vec<FileChunk> },
    Lnk,
    Sock,
    Wht,
}

impl InodeMode {
    fn from_capnp(reader: metadata_capnp::inode::mode::Reader<'_>) -> Result<Self> {
        match reader.which() {
            Ok(metadata_capnp::inode::mode::Unknown(())) => Ok(InodeMode::Unknown),
            Ok(metadata_capnp::inode::mode::Fifo(())) => Ok(InodeMode::Fifo),
            Ok(metadata_capnp::inode::mode::Lnk(())) => Ok(InodeMode::Lnk),
            Ok(metadata_capnp::inode::mode::Sock(())) => Ok(InodeMode::Sock),
            Ok(metadata_capnp::inode::mode::Wht(())) => Ok(InodeMode::Wht),
            Ok(metadata_capnp::inode::mode::Chr(reader)) => {
                let r = reader?;
                Ok(InodeMode::Chr {
                    major: r.get_major(),
                    minor: r.get_minor(),
                })
            }
            Ok(metadata_capnp::inode::mode::Blk(reader)) => {
                let r = reader?;
                Ok(InodeMode::Blk {
                    major: r.get_major(),
                    minor: r.get_minor(),
                })
            }
            Ok(metadata_capnp::inode::mode::File(reader)) => {
                let r = reader?;
                let mut chunks = Vec::new();
                for chunk in r.iter() {
                    chunks.try_push(FileChunk::from_capnp(chunk)?)?;
                }

                Ok(InodeMode::File { chunks })
            }
            Ok(metadata_capnp::inode::mode::Dir(reader)) => {
                let r = reader?;
                let mut entries = Vec::new();
                for entry in r.get_entries()?.iter() {
                    let ino = entry.get_ino();
                    let dir_entry = Vec::from_iter_fallible(entry.get_name()?.iter().cloned())?;
                    entries.try_push(DirEnt {
                        ino,
                        name: dir_entry,
                    })?;
                }
                let look_below = r.get_look_below();
                Ok(InodeMode::Dir {
                    dir_list: DirList {
                        look_below,
                        entries,
                    },
                })
            }
            Err(::capnp::NotInSchema(_e)) => Err(WireFormatError::InvalidSerializedData),
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct InodeAdditional {
    pub(crate) xattrs: Vec<Xattr>,
    pub(crate) symlink_target: Option<Vec<u8>>,
}

impl InodeAdditional {
    pub(crate) fn from_capnp(
        reader: metadata_capnp::inode_additional::Reader<'_>,
    ) -> Result<Option<Self>> {
        if !(reader.has_xattrs() || reader.has_symlink_target()) {
            return Ok(None);
        }

        let mut xattrs = Vec::new();
        if reader.has_xattrs() {
            for capnp_xattr in reader.get_xattrs()? {
                let xattr = Xattr::from_capnp(capnp_xattr)?;
                xattrs.try_push(xattr)?;
            }
        }

        let symlink_target = if reader.has_symlink_target() {
            Some(Vec::from_iter_fallible(
                reader.get_symlink_target()?.iter().cloned(),
            )?)
        } else {
            None
        };

        Ok(Some(InodeAdditional {
            xattrs,
            symlink_target,
        }))
    }
}

#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Xattr {
    pub(crate) key: Vec<u8>,
    pub(crate) val: Vec<u8>,
}

impl Xattr {
    pub(crate) fn from_capnp(reader: metadata_capnp::xattr::Reader<'_>) -> Result<Self> {
        let key = Vec::from_iter_fallible(reader.get_key()?.iter().cloned())?;
        let val = Vec::from_iter_fallible(reader.get_val()?.iter().cloned())?;
        Ok(Xattr { key, val })
    }
}

pub(crate) struct MetadataBlob {
    reader: message::TypedReader<
        ::capnp::serialize::NoAllocBufferSegments<Vec<u8>>,
        metadata_capnp::inode_vector::Owned,
    >,
}

impl MetadataBlob {
    pub(crate) fn new(f: file::RegularFile) -> Result<MetadataBlob> {
        // We know the loaded message is safe, so we're allowing unlimited reads.
        let unlimited_reads = message::ReaderOptions {
            traversal_limit_in_words: None,
            nesting_limit: 64,
        };
        let metadata_buffer = f.read_to_end()?;
        let segments = ::capnp::serialize::NoAllocBufferSegments::from_buffer(
            metadata_buffer,
            unlimited_reads,
        )?;
        let reader = message::Reader::new(segments, unlimited_reads).into_typed();

        Ok(MetadataBlob { reader })
    }

    pub(crate) fn get_inode_vector(
        &self,
    ) -> ::capnp::Result<::capnp::struct_list::Reader<'_, metadata_capnp::inode::Owned>> {
        self.reader.get()?.get_inodes()
    }

    pub(crate) fn find_inode(&self, ino: Ino) -> Result<Option<metadata_capnp::inode::Reader<'_>>> {
        let mut left = 0;
        let inodes = self.get_inode_vector()?;
        let mut right = inodes.len() - 1;

        while left <= right {
            let mid = left + (right - left) / 2;
            let i = inodes.get(mid);

            if i.get_ino() == ino {
                return Ok(Some(i));
            }

            if i.get_ino() < ino {
                left = mid + 1;
            } else {
                // don't underflow...
                if mid == 0 {
                    break;
                }
                right = mid - 1;
            };
        }

        Ok(None)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct Digest([u8; SHA256_BLOCK_SIZE]);

impl Digest {
    pub(crate) fn underlying(&self) -> [u8; SHA256_BLOCK_SIZE] {
        let mut dest = [0_u8; SHA256_BLOCK_SIZE];
        dest.copy_from_slice(&self.0);
        dest
    }
}

impl fmt::Display for Digest {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut hex_string =
            Vec::from_iter_fallible(encode_hex_iter(&self.underlying())).map_err(|_| fmt::Error)?;
        // append NUL character
        hex_string.try_push(0).map_err(|_| fmt::Error)?;
        let hex_string = CStr::from_bytes_with_nul(&hex_string).map_err(|_| fmt::Error)?;
        write!(f, "{}", hex_string)
    }
}

impl TryFrom<&CStr> for Digest {
    type Error = FromHexError;
    fn try_from(s: &CStr) -> kernel::error::Result<Self, Self::Error> {
        let digest = hex::decode(s)?;
        let digest: [u8; SHA256_BLOCK_SIZE] = digest
            .try_into()
            .map_err(|_| FromHexError::InvalidStringLength)?;
        Ok(Digest(digest))
    }
}

impl TryFrom<BlobRef> for Digest {
    type Error = WireFormatError;
    fn try_from(v: BlobRef) -> kernel::error::Result<Self, Self::Error> {
        Ok(Digest(v.digest))
    }
}

impl TryFrom<&BlobRef> for Digest {
    type Error = WireFormatError;
    fn try_from(v: &BlobRef) -> kernel::error::Result<Self, Self::Error> {
        Ok(Digest(v.digest))
    }
}

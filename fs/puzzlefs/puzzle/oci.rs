use crate::puzzle::error::Result;
use crate::puzzle::types::{Digest, MetadataBlob, Rootfs};
use kernel::c_str;
use kernel::file;
use kernel::file::RegularFile;
use kernel::mount::Vfsmount;
use kernel::pr_debug;
use kernel::str::{CStr, CString};

#[derive(Debug)]
pub(crate) struct Image {
    pub(crate) vfs_mount: Vfsmount,
}

impl Image {
    pub(crate) fn open(vfsmount: Vfsmount) -> Result<Self> {
        Ok(Image {
            vfs_mount: vfsmount,
        })
    }

    pub(crate) fn blob_path_relative(&self) -> &CStr {
        c_str!("blobs/sha256")
    }

    fn open_raw_blob(&self, digest: &Digest) -> Result<RegularFile> {
        let filename =
            CString::try_from_fmt(format_args!("{}/{digest}", self.blob_path_relative()))?;
        pr_debug!("trying to open {:?}\n", &*filename);

        let file = RegularFile::from_path_in_root_mnt(
            &self.vfs_mount,
            &filename,
            file::flags::O_RDONLY.try_into().unwrap(),
            0,
        )?;

        Ok(file)
    }

    pub(crate) fn open_metadata_blob(&self, digest: &Digest) -> Result<MetadataBlob> {
        let f = self.open_raw_blob(digest)?;
        MetadataBlob::new(f)
    }

    pub(crate) fn open_rootfs_blob(&self, path: &CStr) -> Result<Rootfs> {
        let digest = Digest::try_from(path)?;
        let rootfs = Rootfs::open(self.open_raw_blob(&digest)?)?;
        Ok(rootfs)
    }
}

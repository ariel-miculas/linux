// SPDX-License-Identifier: GPL-2.0

#include <linux/file.h>

struct file *rust_helper_get_file(struct file *f)
{
    return get_file(f);
}
EXPORT_SYMBOL_GPL(rust_helper_get_file);

loff_t rust_helper_i_size_read(const struct inode *inode)
{
    return i_size_read(inode);
}
EXPORT_SYMBOL_GPL(rust_helper_i_size_read);

struct dentry *rust_helper_dget(struct dentry *dentry)
{
    return dget(dentry);
}
EXPORT_SYMBOL_GPL(rust_helper_dget);

void rust_helper_i_uid_write(struct inode *inode, uid_t uid)
{
    i_uid_write(inode, uid);
}
EXPORT_SYMBOL_GPL(rust_helper_i_uid_write);

void rust_helper_i_gid_write(struct inode *inode, gid_t gid)
{
    i_gid_write(inode, gid);
}
EXPORT_SYMBOL_GPL(rust_helper_i_gid_write);

void rust_helper_inode_lock_shared(struct inode *inode)
{
    inode_lock_shared(inode);
}
EXPORT_SYMBOL_GPL(rust_helper_inode_lock_shared);

void rust_helper_inode_unlock_shared(struct inode *inode)
{
    inode_unlock_shared(inode);
}
EXPORT_SYMBOL_GPL(rust_helper_inode_unlock_shared);

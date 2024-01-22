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

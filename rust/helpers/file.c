// SPDX-License-Identifier: GPL-2.0

#include <linux/file.h>
#include <linux/pagemap.h>

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
void *rust_helper_kmap(struct page *page)
{
	return kmap(page);
}
EXPORT_SYMBOL_GPL(rust_helper_kmap);

void rust_helper_kunmap(struct page *page)
{
	kunmap(page);
}
EXPORT_SYMBOL_GPL(rust_helper_kunmap);

void rust_helper_folio_get(struct folio *folio)
{
	folio_get(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_get);

void rust_helper_folio_put(struct folio *folio)
{
	folio_put(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_put);

struct folio *rust_helper_folio_alloc(gfp_t gfp, unsigned int order)
{
	return folio_alloc(gfp, order);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_alloc);

struct page *rust_helper_folio_page(struct folio *folio, size_t n)
{
	return folio_page(folio, n);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_page);

loff_t rust_helper_folio_pos(struct folio *folio)
{
	return folio_pos(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_pos);

size_t rust_helper_folio_size(struct folio *folio)
{
	return folio_size(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_size);

void rust_helper_folio_lock(struct folio *folio)
{
	folio_lock(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_lock);

bool rust_helper_folio_test_uptodate(struct folio *folio)
{
	return folio_test_uptodate(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_test_uptodate);

void rust_helper_folio_mark_uptodate(struct folio *folio)
{
	folio_mark_uptodate(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_mark_uptodate);

bool rust_helper_folio_test_highmem(struct folio *folio)
{
	return folio_test_highmem(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_folio_test_highmem);

void rust_helper_flush_dcache_folio(struct folio *folio)
{
	flush_dcache_folio(folio);
}
EXPORT_SYMBOL_GPL(rust_helper_flush_dcache_folio);

void *rust_helper_kmap_local_folio(struct folio *folio, size_t offset)
{
	return kmap_local_folio(folio, offset);
}
EXPORT_SYMBOL_GPL(rust_helper_kmap_local_folio);

void rust_helper_mapping_set_large_folios(struct address_space *mapping)
{
    mapping_set_large_folios(mapping);
}
EXPORT_SYMBOL_GPL(rust_helper_mapping_set_large_folios);

// SPDX-License-Identifier: GPL-2.0

#include <linux/file.h>

struct file *rust_helper_get_file(struct file *f)
{
    return get_file(f);
}
EXPORT_SYMBOL_GPL(rust_helper_get_file);

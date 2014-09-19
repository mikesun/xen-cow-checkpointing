#include <xen/lib.h>       /* for printk() used in stub */
#include <xen/types.h>
#include <xen/kexec.h>
#include <public/kexec.h>

void machine_crash_shutdown(void)
{
    printk("STUB: " __FILE__ ": %s: not implemented\n", __FUNCTION__);
}

/*
 * Local variables:
 * mode: C
 * c-set-style: "BSD"
 * c-basic-offset: 4
 * tab-width: 4
 * indent-tabs-mode: nil
 * End:
 */


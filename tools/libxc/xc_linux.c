/******************************************************************************
 *
 * Copyright 2006 Sun Microsystems, Inc.  All rights reserved.
 * Use is subject to license terms.
 *
 * xc_gnttab functions:
 * Copyright (c) 2007, D G Murray <Derek.Murray@cl.cam.ac.uk>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, version 2 of the
 * License.
 */

#include "xc_private.h"

#include <xen/memory.h>
#include <xen/sys/evtchn.h>
#include <xen/sys/gntdev.h>
#include <unistd.h>
#include <fcntl.h>

int xc_interface_open(void)
{
    int flags, saved_errno;
    int fd = open("/proc/xen/privcmd", O_RDWR);

    if ( fd == -1 )
    {
        PERROR("Could not obtain handle on privileged command interface");
        return -1;
    }

    /* Although we return the file handle as the 'xc handle' the API
       does not specify / guarentee that this integer is in fact
       a file handle. Thus we must take responsiblity to ensure
       it doesn't propagate (ie leak) outside the process */
    if ( (flags = fcntl(fd, F_GETFD)) < 0 )
    {
        PERROR("Could not get file handle flags");
        goto error;
    }
    flags |= FD_CLOEXEC;
    if ( fcntl(fd, F_SETFD, flags) < 0 )
    {
        PERROR("Could not set file handle flags");
        goto error;
    }

    return fd;

 error:
    saved_errno = errno;
    close(fd);
    errno = saved_errno;
    return -1;
}

int xc_interface_close(int xc_handle)
{
    return close(xc_handle);
}

void *xc_map_foreign_batch(int xc_handle, uint32_t dom, int prot,
                           xen_pfn_t *arr, int num)
{
    privcmd_mmapbatch_t ioctlx;
    void *addr;
    addr = mmap(NULL, num*PAGE_SIZE, prot, MAP_SHARED, xc_handle, 0);
    if ( addr == MAP_FAILED ) {
        perror("xc_map_foreign_batch: mmap failed");
        return NULL;
    }

    ioctlx.num=num;
    ioctlx.dom=dom;
    ioctlx.addr=(unsigned long)addr;
    ioctlx.arr=arr;
    if ( ioctl(xc_handle, IOCTL_PRIVCMD_MMAPBATCH, &ioctlx) < 0 )
    {
        int saved_errno = errno;
        perror("xc_map_foreign_batch: ioctl failed");
        (void)munmap(addr, num*PAGE_SIZE);
        errno = saved_errno;
        return NULL;
    }
    return addr;

}

void *xc_map_foreign_range(int xc_handle, uint32_t dom,
                           int size, int prot,
                           unsigned long mfn)
{
    privcmd_mmap_t ioctlx;
    privcmd_mmap_entry_t entry;
    void *addr;
    addr = mmap(NULL, size, prot, MAP_SHARED, xc_handle, 0);
    if ( addr == MAP_FAILED ) {
        perror("xc_map_foreign_range: mmap failed");
        return NULL;
    }

    ioctlx.num=1;
    ioctlx.dom=dom;
    ioctlx.entry=&entry;
    entry.va=(unsigned long) addr;
    entry.mfn=mfn;
    entry.npages=(size+PAGE_SIZE-1)>>PAGE_SHIFT;
    if ( ioctl(xc_handle, IOCTL_PRIVCMD_MMAP, &ioctlx) < 0 )
    {
        int saved_errno = errno;
        perror("xc_map_foreign_range: ioctl failed");
        (void)munmap(addr, size);
        errno = saved_errno;
        return NULL;
    }
    return addr;
}

int xc_map_foreign_ranges(int xc_handle, uint32_t dom,
                          privcmd_mmap_entry_t *entries, int nr)
{
    privcmd_mmap_t ioctlx;

    ioctlx.num   = nr;
    ioctlx.dom   = dom;
    ioctlx.entry = entries;

    return ioctl(xc_handle, IOCTL_PRIVCMD_MMAP, &ioctlx);
}

static int do_privcmd(int xc_handle, unsigned int cmd, unsigned long data)
{
    return ioctl(xc_handle, cmd, data);
}

int do_xen_hypercall(int xc_handle, privcmd_hypercall_t *hypercall)
{
    return do_privcmd(xc_handle,
                      IOCTL_PRIVCMD_HYPERCALL,
                      (unsigned long)hypercall);
}

#define MTAB "/proc/mounts"
#define MAX_PATH 255
#define _STR(x) #x
#define STR(x) _STR(x)

static int find_sysfsdir(char *sysfsdir)
{
    FILE *fp;
    char type[MAX_PATH + 1];

    if ( (fp = fopen(MTAB, "r")) == NULL )
        return -1;

    while ( fscanf(fp, "%*s %"
                   STR(MAX_PATH)
                   "s %"
                   STR(MAX_PATH)
                   "s %*s %*d %*d\n",
                   sysfsdir, type) == 2 )
    {
        if ( strncmp(type, "sysfs", 5) == 0 )
            break;
    }

    fclose(fp);

    return ((strncmp(type, "sysfs", 5) == 0) ? 0 : -1);
}

int xc_find_device_number(const char *name)
{
    FILE *fp;
    int i, major, minor;
    char sysfsdir[MAX_PATH + 1];
    static char *classlist[] = { "xen", "misc" };

    for ( i = 0; i < (sizeof(classlist) / sizeof(classlist[0])); i++ )
    {
        if ( find_sysfsdir(sysfsdir) < 0 )
            goto not_found;

        /* <base>/class/<classname>/<devname>/dev */
        strncat(sysfsdir, "/class/", MAX_PATH);
        strncat(sysfsdir, classlist[i], MAX_PATH);
        strncat(sysfsdir, "/", MAX_PATH);
        strncat(sysfsdir, name, MAX_PATH);
        strncat(sysfsdir, "/dev", MAX_PATH);

        if ( (fp = fopen(sysfsdir, "r")) != NULL )
            goto found;
    }

 not_found:
    errno = -ENOENT;
    return -1;

 found:
    if ( fscanf(fp, "%d:%d", &major, &minor) != 2 )
    {
        fclose(fp);
        goto not_found;
    }

    fclose(fp);

    return makedev(major, minor);
}

#define EVTCHN_DEV_NAME  "/dev/xen/evtchn"

int xc_evtchn_open(void)
{
    struct stat st;
    int fd;
    int devnum;

    devnum = xc_find_device_number("evtchn");

    /* Make sure any existing device file links to correct device. */
    if ( (lstat(EVTCHN_DEV_NAME, &st) != 0) || !S_ISCHR(st.st_mode) ||
         (st.st_rdev != devnum) )
        (void)unlink(EVTCHN_DEV_NAME);

 reopen:
    if ( (fd = open(EVTCHN_DEV_NAME, O_RDWR)) == -1 )
    {
        if ( (errno == ENOENT) &&
            ((mkdir("/dev/xen", 0755) == 0) || (errno == EEXIST)) &&
             (mknod(EVTCHN_DEV_NAME, S_IFCHR|0600, devnum) == 0) )
            goto reopen;

        PERROR("Could not open event channel interface");
        return -1;
    }

    return fd;
}

int xc_evtchn_close(int xce_handle)
{
    return close(xce_handle);
}

int xc_evtchn_fd(int xce_handle)
{
    return xce_handle;
}

int xc_evtchn_notify(int xce_handle, evtchn_port_t port)
{
    struct ioctl_evtchn_notify notify;

    notify.port = port;

    return ioctl(xce_handle, IOCTL_EVTCHN_NOTIFY, &notify);
}

evtchn_port_or_error_t
xc_evtchn_bind_unbound_port(int xce_handle, int domid)
{
    struct ioctl_evtchn_bind_unbound_port bind;

    bind.remote_domain = domid;

    return ioctl(xce_handle, IOCTL_EVTCHN_BIND_UNBOUND_PORT, &bind);
}

evtchn_port_or_error_t
xc_evtchn_bind_interdomain(int xce_handle, int domid,
                           evtchn_port_t remote_port)
{
    struct ioctl_evtchn_bind_interdomain bind;

    bind.remote_domain = domid;
    bind.remote_port = remote_port;

    return ioctl(xce_handle, IOCTL_EVTCHN_BIND_INTERDOMAIN, &bind);
}

evtchn_port_or_error_t
xc_evtchn_bind_virq(int xce_handle, unsigned int virq)
{
    struct ioctl_evtchn_bind_virq bind;

    bind.virq = virq;

    return ioctl(xce_handle, IOCTL_EVTCHN_BIND_VIRQ, &bind);
}

int xc_evtchn_unbind(int xce_handle, evtchn_port_t port)
{
    struct ioctl_evtchn_unbind unbind;

    unbind.port = port;

    return ioctl(xce_handle, IOCTL_EVTCHN_UNBIND, &unbind);
}

evtchn_port_or_error_t
xc_evtchn_pending(int xce_handle)
{
    evtchn_port_t port;

    if ( read_exact(xce_handle, (char *)&port, sizeof(port)) == -1 )
        return -1;

    return port;
}

int xc_evtchn_unmask(int xce_handle, evtchn_port_t port)
{
    return write_exact(xce_handle, (char *)&port, sizeof(port));
}

/* Optionally flush file to disk and discard page cache */
void discard_file_cache(int fd, int flush) 
{
    off_t cur = 0;
    int saved_errno = errno;

    if ( flush && (fsync(fd) < 0) )
    {
        /*PERROR("Failed to flush file: %s", strerror(errno));*/
        goto out;
    }

    /* 
     * Calculate last page boundary of amount written so far 
     * unless we are flushing in which case entire cache
     * is discarded.
     */
    if ( !flush )
    {
        if ( (cur = lseek(fd, 0, SEEK_CUR)) == (off_t)-1 )
            cur = 0;
        cur &= ~(PAGE_SIZE-1);
    }

    /* Discard from the buffer cache. */
    if ( posix_fadvise64(fd, 0, cur, POSIX_FADV_DONTNEED) < 0 )
    {
        /*PERROR("Failed to discard cache: %s", strerror(errno));*/
        goto out;
    }

 out:
    errno = saved_errno;
}

#define GNTTAB_DEV_NAME "/dev/xen/gntdev"

int xc_gnttab_open(void)
{
    struct stat st;
    int fd;
    int devnum;
    
    devnum = xc_find_device_number("gntdev");
    
    /* Make sure any existing device file links to correct device. */
    if ( (lstat(GNTTAB_DEV_NAME, &st) != 0) || !S_ISCHR(st.st_mode) ||
         (st.st_rdev != devnum) )
        (void)unlink(GNTTAB_DEV_NAME);
    
reopen:
    if ( (fd = open(GNTTAB_DEV_NAME, O_RDWR)) == -1 )
    {
        if ( (errno == ENOENT) &&
             ((mkdir("/dev/xen", 0755) == 0) || (errno == EEXIST)) &&
             (mknod(GNTTAB_DEV_NAME, S_IFCHR|0600, devnum) == 0) )
            goto reopen;
        
        PERROR("Could not open grant table interface");
        return -1;
    }
    
    return fd;
}

int xc_gnttab_close(int xcg_handle)
{
    return close(xcg_handle);
}

void *xc_gnttab_map_grant_ref(int xcg_handle,
                              uint32_t domid,
                              uint32_t ref,
                              int prot)
{
    struct ioctl_gntdev_map_grant_ref map;
    void *addr;
    
    map.count = 1;
    map.refs[0].domid = domid;
    map.refs[0].ref   = ref;

    if ( ioctl(xcg_handle, IOCTL_GNTDEV_MAP_GRANT_REF, &map) )
        return NULL;
    
    addr = mmap(NULL, PAGE_SIZE, prot, MAP_SHARED, xcg_handle, map.index);
    if ( addr == MAP_FAILED )
    {
        int saved_errno = errno;
        struct ioctl_gntdev_unmap_grant_ref unmap_grant;
        /* Unmap the driver slots used to store the grant information. */
        perror("xc_gnttab_map_grant_ref: mmap failed");
        unmap_grant.index = map.index;
        unmap_grant.count = 1;
        ioctl(xcg_handle, IOCTL_GNTDEV_UNMAP_GRANT_REF, &unmap_grant);
        errno = saved_errno;
        return NULL;
    }
    
    return addr;
}

void *xc_gnttab_map_grant_refs(int xcg_handle,
                               uint32_t count,
                               uint32_t *domids,
                               uint32_t *refs,
                               int prot)
{
    struct ioctl_gntdev_map_grant_ref *map;
    void *addr = NULL;
    int i;
    
    map = malloc(sizeof(*map) +
                 (count-1) * sizeof(struct ioctl_gntdev_map_grant_ref));
    if ( map == NULL )
        return NULL;

    for ( i = 0; i < count; i++ )
    {
        map->refs[i].domid = domids[i];
        map->refs[i].ref   = refs[i];
    }

    map->count = count;
    
    if ( ioctl(xcg_handle, IOCTL_GNTDEV_MAP_GRANT_REF, map) )
        goto out;

    addr = mmap(NULL, PAGE_SIZE * count, prot, MAP_SHARED, xcg_handle,
                map->index);
    if ( addr == MAP_FAILED )
    {
        int saved_errno = errno;
        struct ioctl_gntdev_unmap_grant_ref unmap_grant;
        /* Unmap the driver slots used to store the grant information. */
        perror("xc_gnttab_map_grant_refs: mmap failed");
        unmap_grant.index = map->index;
        unmap_grant.count = count;
        ioctl(xcg_handle, IOCTL_GNTDEV_UNMAP_GRANT_REF, &unmap_grant);
        errno = saved_errno;
        addr = NULL;
    }

 out:
    free(map);
    return addr;
}

int xc_gnttab_munmap(int xcg_handle,
                     void *start_address,
                     uint32_t count)
{
    struct ioctl_gntdev_get_offset_for_vaddr get_offset;
    struct ioctl_gntdev_unmap_grant_ref unmap_grant;
    int rc;

    if ( start_address == NULL )
    {
        errno = EINVAL;
        return -1;
    }

    /* First, it is necessary to get the offset which was initially used to
     * mmap() the pages.
     */
    get_offset.vaddr = (unsigned long)start_address;
    if ( (rc = ioctl(xcg_handle, IOCTL_GNTDEV_GET_OFFSET_FOR_VADDR, 
                     &get_offset)) )
        return rc;

    if ( get_offset.count != count )
    {
        errno = EINVAL;
        return -1;
    }

    /* Next, unmap the memory. */
    if ( (rc = munmap(start_address, count * getpagesize())) )
        return rc;
    
    /* Finally, unmap the driver slots used to store the grant information. */
    unmap_grant.index = get_offset.offset;
    unmap_grant.count = count;
    if ( (rc = ioctl(xcg_handle, IOCTL_GNTDEV_UNMAP_GRANT_REF, &unmap_grant)) )
        return rc;

    return 0;
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

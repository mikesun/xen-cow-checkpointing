#include <stdarg.h>
#include <stdlib.h>
#include <sys/types.h>
#include <fcntl.h>
#include <unistd.h>
#include <xenctrl.h>
#include <xen/io/xenbus.h>
#include <xen/io/fbif.h>
#include <xen/io/kbdif.h>
#include <xen/io/protocols.h>
#include <stdbool.h>
#include <xen/event_channel.h>
#include <sys/mman.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <xs.h>

#include "xenfb.h"

#ifndef BTN_LEFT
#define BTN_LEFT 0x110 /* from <linux/input.h> */
#endif

struct xenfb;

struct xenfb_device {
	const char *devicetype;
	char nodename[64];	/* backend xenstore dir */
	char otherend[64];	/* frontend xenstore dir */
	int otherend_id;	/* frontend domid */
	enum xenbus_state state; /* backend state */
	void *page;		/* shared page */
	evtchn_port_t port;
	struct xenfb *xenfb;
};

struct xenfb {
	DisplayState *ds;       /* QEMU graphical console state */
	int evt_xch;		/* event channel driver handle */
	int xc;			/* hypervisor interface handle */
	struct xs_handle *xsh;	/* xs daemon handle */
	struct xenfb_device fb, kbd;
	void *pixels;           /* guest framebuffer data */
	size_t fb_len;		/* size of framebuffer */
	int row_stride;         /* width of one row in framebuffer */
	int depth;              /* colour depth of guest framebuffer */
	int width;              /* pixel width of guest framebuffer */
	int height;             /* pixel height of guest framebuffer */
	int abs_pointer_wanted; /* Whether guest supports absolute pointer */
	int button_state;       /* Last seen pointer button state */
	char protocol[64];	/* frontend protocol */
};

/* Functions for frontend/backend state machine*/
static int xenfb_wait_for_frontend(struct xenfb_device *dev, IOHandler *handler);
static int xenfb_wait_for_backend(struct xenfb_device *dev, IOHandler *handler);
static void xenfb_backend_created_kbd(void *opaque);
static void xenfb_backend_created_fb(void *opaque);
static void xenfb_frontend_initialized_kbd(void *opaque);
static void xenfb_frontend_initialized_fb(void *opaque);
static void xenfb_frontend_connected_kbd(void *opaque);

/* Helper functions for checking state of frontend/backend devices */
static int xenfb_frontend_connected(struct xenfb_device *dev);
static int xenfb_frontend_initialized(struct xenfb_device *dev);
static int xenfb_backend_created(struct xenfb_device *dev);

/* Functions which tie the PVFB into the QEMU device model */
static void xenfb_key_event(void *opaque, int keycode);
static void xenfb_mouse_event(void *opaque,
			      int dx, int dy, int dz, int button_state);
static void xenfb_guest_copy(struct xenfb *xenfb, int x, int y, int w, int h);
static void xenfb_update(void *opaque);
static void xenfb_invalidate(void *opaque);
static void xenfb_screen_dump(void *opaque, const char *name);
static int xenfb_register_console(struct xenfb *xenfb);

/*
 * Tables to map from scancode to Linux input layer keycode.
 * Scancodes are hardware-specific.  These maps assumes a 
 * standard AT or PS/2 keyboard which is what QEMU feeds us.
 */
static const unsigned char atkbd_set2_keycode[512] = {

	  0, 67, 65, 63, 61, 59, 60, 88,  0, 68, 66, 64, 62, 15, 41,117,
	  0, 56, 42, 93, 29, 16,  2,  0,  0,  0, 44, 31, 30, 17,  3,  0,
	  0, 46, 45, 32, 18,  5,  4, 95,  0, 57, 47, 33, 20, 19,  6,183,
	  0, 49, 48, 35, 34, 21,  7,184,  0,  0, 50, 36, 22,  8,  9,185,
	  0, 51, 37, 23, 24, 11, 10,  0,  0, 52, 53, 38, 39, 25, 12,  0,
	  0, 89, 40,  0, 26, 13,  0,  0, 58, 54, 28, 27,  0, 43,  0, 85,
	  0, 86, 91, 90, 92,  0, 14, 94,  0, 79,124, 75, 71,121,  0,  0,
	 82, 83, 80, 76, 77, 72,  1, 69, 87, 78, 81, 74, 55, 73, 70, 99,

	  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,  0,
	217,100,255,  0, 97,165,  0,  0,156,  0,  0,  0,  0,  0,  0,125,
	173,114,  0,113,  0,  0,  0,126,128,  0,  0,140,  0,  0,  0,127,
	159,  0,115,  0,164,  0,  0,116,158,  0,150,166,  0,  0,  0,142,
	157,  0,  0,  0,  0,  0,  0,  0,155,  0, 98,  0,  0,163,  0,  0,
	226,  0,  0,  0,  0,  0,  0,  0,  0,255, 96,  0,  0,  0,143,  0,
	  0,  0,  0,  0,  0,  0,  0,  0,  0,107,  0,105,102,  0,  0,112,
	110,111,108,112,106,103,  0,119,  0,118,109,  0, 99,104,119,  0,

};

static const unsigned char atkbd_unxlate_table[128] = {

	  0,118, 22, 30, 38, 37, 46, 54, 61, 62, 70, 69, 78, 85,102, 13,
	 21, 29, 36, 45, 44, 53, 60, 67, 68, 77, 84, 91, 90, 20, 28, 27,
	 35, 43, 52, 51, 59, 66, 75, 76, 82, 14, 18, 93, 26, 34, 33, 42,
	 50, 49, 58, 65, 73, 74, 89,124, 17, 41, 88,  5,  6,  4, 12,  3,
	 11,  2, 10,  1,  9,119,126,108,117,125,123,107,115,116,121,105,
	114,122,112,113,127, 96, 97,120,  7, 15, 23, 31, 39, 47, 55, 63,
	 71, 79, 86, 94,  8, 16, 24, 32, 40, 48, 56, 64, 72, 80, 87,111,
	 19, 25, 57, 81, 83, 92, 95, 98, 99,100,101,103,104,106,109,110

};

static unsigned char scancode2linux[512];

static int xenfb_xs_scanf1(struct xs_handle *xsh,
			   const char *dir, const char *node,
			   const char *fmt, void *dest)
{
	char buf[1024];
	char *p;
	int ret;

	if (snprintf(buf, sizeof(buf), "%s/%s", dir, node) >= sizeof(buf)) {
		errno = ENOENT;
		return -1;
        }
	p = xs_read(xsh, XBT_NULL, buf, NULL);
	if (!p) {
		errno = ENOENT;
		return -1;
        }
	ret = sscanf(p, fmt, dest);
	free(p);
	if (ret != 1) {
		errno = EDOM;
		return -1;
        }
	return ret;
}

static int xenfb_xs_printf(struct xs_handle *xsh,
			   const char *dir, const char *node, char *fmt, ...)
{
	va_list ap;
	char key[1024];
	char val[1024];
	int n;

	if (snprintf(key, sizeof(key), "%s/%s", dir, node) >= sizeof(key)) {
		errno = ENOENT;
		return -1;
        }

	va_start(ap, fmt);
	n = vsnprintf(val, sizeof(val), fmt, ap);
	va_end(ap);
	if (n >= sizeof(val)) {
		errno = ENOSPC; /* close enough */
		return -1;
	}

	if (!xs_write(xsh, XBT_NULL, key, val, n))
		return -1;
	return 0;
}

static void xenfb_device_init(struct xenfb_device *dev,
			      const char *type,
			      struct xenfb *xenfb)
{
	dev->devicetype = type;
	dev->otherend_id = -1;
	dev->port = -1;
	dev->xenfb = xenfb;
}

static char *xenfb_path_in_dom(struct xs_handle *xsh,
                               char *buf, size_t size,
                               unsigned domid, const char *fmt, ...)
{
        va_list ap;
        char *domp = xs_get_domain_path(xsh, domid);
        int n;

        if (domp == NULL)
                return NULL;

        n = snprintf(buf, size, "%s/", domp);
        free(domp);
        if (n >= size)
                return NULL;

        va_start(ap, fmt);
        n += vsnprintf(buf + n, size - n, fmt, ap);
        va_end(ap);
        if (n >= size)
                return NULL;

        return buf;
}

static int xenfb_device_set_domain(struct xenfb_device *dev, int domid)
{
        dev->otherend_id = domid;

        if (!xenfb_path_in_dom(dev->xenfb->xsh,
                               dev->otherend, sizeof(dev->otherend),
                               domid, "device/%s/0", dev->devicetype)) {
                errno = ENOENT;
                return -1;
        }
        if (!xenfb_path_in_dom(dev->xenfb->xsh,
                               dev->nodename, sizeof(dev->nodename),
                               0, "backend/%s/%d/0", dev->devicetype, domid)) {
                errno = ENOENT;
                return -1;
        }

        return 0;
}

struct xenfb *xenfb_new(int domid, DisplayState *ds)
{
	struct xenfb *xenfb = qemu_malloc(sizeof(struct xenfb));
	int serrno;
	int i;

	if (xenfb == NULL)
		return NULL;

	/* Prepare scancode mapping table */
	for (i = 0; i < 128; i++) {
		scancode2linux[i] = atkbd_set2_keycode[atkbd_unxlate_table[i]];
		scancode2linux[i | 0x80] = 
			atkbd_set2_keycode[atkbd_unxlate_table[i] | 0x80];
	}

	memset(xenfb, 0, sizeof(*xenfb));
	xenfb->evt_xch = xenfb->xc = -1;
	xenfb_device_init(&xenfb->fb, "vfb", xenfb);
	xenfb_device_init(&xenfb->kbd, "vkbd", xenfb);

	xenfb->evt_xch = xc_evtchn_open();
	if (xenfb->evt_xch == -1)
		goto fail;

	xenfb->xc = xc_interface_open();
	if (xenfb->xc == -1)
		goto fail;

	xenfb->xsh = xs_daemon_open();
	if (!xenfb->xsh)
		goto fail;

	xenfb->ds = ds;
	xenfb_device_set_domain(&xenfb->fb, domid);
	xenfb_device_set_domain(&xenfb->kbd, domid);

	fprintf(stderr, "FB: Waiting for KBD backend creation\n");
	xenfb_wait_for_backend(&xenfb->kbd, xenfb_backend_created_kbd);

	return xenfb;

 fail:
	serrno = errno;
	xenfb_shutdown(xenfb);
	errno = serrno;
	return NULL;
}


static enum xenbus_state xenfb_read_state(struct xs_handle *xsh,
					  const char *dir)
{
	int ret, state;

	ret = xenfb_xs_scanf1(xsh, dir, "state", "%d", &state);
	if (ret < 0)
		return XenbusStateUnknown;

	if ((unsigned)state > XenbusStateClosed)
		state = XenbusStateUnknown;
	return state;
}

static int xenfb_switch_state(struct xenfb_device *dev,
			      enum xenbus_state state)
{
	struct xs_handle *xsh = dev->xenfb->xsh;

	if (xenfb_xs_printf(xsh, dev->nodename, "state", "%d", state) < 0)
		return -1;
	dev->state = state;
	return 0;
}


static int xenfb_hotplug(struct xenfb_device *dev)
{
	if (xenfb_xs_printf(dev->xenfb->xsh, dev->nodename,
			    "hotplug-status", "connected"))
		return -1;
	return 0;
}

static void xenfb_copy_mfns(int mode, int count, unsigned long *dst, void *src)
{
	uint32_t *src32 = src;
	uint64_t *src64 = src;
	int i;

	for (i = 0; i < count; i++)
		dst[i] = (mode == 32) ? src32[i] : src64[i];
}

static int xenfb_map_fb(struct xenfb *xenfb, int domid)
{
	struct xenfb_page *page = xenfb->fb.page;
	int n_fbmfns;
	int n_fbdirs;
	unsigned long *pgmfns = NULL;
	unsigned long *fbmfns = NULL;
	void *map, *pd;
	int mode, ret = -1;

	/* default to native */
	pd = page->pd;
	mode = sizeof(unsigned long) * 8;

	if (0 == strlen(xenfb->protocol)) {
		/*
		 * Undefined protocol, some guesswork needed.
		 *
		 * Old frontends which don't set the protocol use
		 * one page directory only, thus pd[1] must be zero.
		 * pd[1] of the 32bit struct layout and the lower
		 * 32 bits of pd[0] of the 64bit struct layout have
		 * the same location, so we can check that ...
		 */
		uint32_t *ptr32 = NULL;
		uint32_t *ptr64 = NULL;
#if defined(__i386__)
		ptr32 = (void*)page->pd;
		ptr64 = ((void*)page->pd) + 4;
#elif defined(__x86_64__)
		ptr32 = ((void*)page->pd) - 4;
		ptr64 = (void*)page->pd;
#endif
		if (ptr32) {
			if (0 == ptr32[1]) {
				mode = 32;
				pd   = ptr32;
			} else {
				mode = 64;
				pd   = ptr64;
			}
		}
#if defined(__x86_64__)
	} else if (0 == strcmp(xenfb->protocol, XEN_IO_PROTO_ABI_X86_32)) {
		/* 64bit dom0, 32bit domU */
		mode = 32;
		pd   = ((void*)page->pd) - 4;
#elif defined(__i386__)
	} else if (0 == strcmp(xenfb->protocol, XEN_IO_PROTO_ABI_X86_64)) {
		/* 32bit dom0, 64bit domU */
		mode = 64;
		pd   = ((void*)page->pd) + 4;
#endif
	}

	n_fbmfns = (xenfb->fb_len + (XC_PAGE_SIZE - 1)) / XC_PAGE_SIZE;
	n_fbdirs = n_fbmfns * mode / 8;
	n_fbdirs = (n_fbdirs + (XC_PAGE_SIZE - 1)) / XC_PAGE_SIZE;

	pgmfns = malloc(sizeof(unsigned long) * n_fbdirs);
	fbmfns = malloc(sizeof(unsigned long) * n_fbmfns);
	if (!pgmfns || !fbmfns)
		goto out;

	xenfb_copy_mfns(mode, n_fbdirs, pgmfns, pd);
	map = xc_map_foreign_pages(xenfb->xc, domid,
				   PROT_READ, pgmfns, n_fbdirs);
	if (map == NULL)
		goto out;
	xenfb_copy_mfns(mode, n_fbmfns, fbmfns, map);
	munmap(map, n_fbdirs * XC_PAGE_SIZE);

	xenfb->pixels = xc_map_foreign_pages(xenfb->xc, domid,
				PROT_READ | PROT_WRITE, fbmfns, n_fbmfns);
	if (xenfb->pixels == NULL)
		goto out;

	ret = 0; /* all is fine */

 out:
	if (pgmfns)
		free(pgmfns);
	if (fbmfns)
		free(fbmfns);
	return ret;
}

static int xenfb_bind(struct xenfb_device *dev)
{
	struct xenfb *xenfb = dev->xenfb;
	unsigned long mfn;
	evtchn_port_t evtchn;

	if (xenfb_xs_scanf1(xenfb->xsh, dev->otherend, "page-ref", "%lu",
			    &mfn) < 0)
		return -1;
	if (xenfb_xs_scanf1(xenfb->xsh, dev->otherend, "event-channel", "%u",
			    &evtchn) < 0)
		return -1;

	dev->port = xc_evtchn_bind_interdomain(xenfb->evt_xch,
					       dev->otherend_id, evtchn);
	if (dev->port == -1)
		return -1;

	dev->page = xc_map_foreign_range(xenfb->xc, dev->otherend_id,
			XC_PAGE_SIZE, PROT_READ | PROT_WRITE, mfn);
	if (dev->page == NULL)
		return -1;

	return 0;
}

static void xenfb_unbind(struct xenfb_device *dev)
{
	if (dev->page) {
		munmap(dev->page, XC_PAGE_SIZE);
		dev->page = NULL;
	}
        if (dev->port >= 0) {
		xc_evtchn_unbind(dev->xenfb->evt_xch, dev->port);
		dev->port = -1;
	}
}


static void xenfb_detach_dom(struct xenfb *xenfb)
{
	xenfb_unbind(&xenfb->fb);
	xenfb_unbind(&xenfb->kbd);
	if (xenfb->pixels) {
		munmap(xenfb->pixels, xenfb->fb_len);
		xenfb->pixels = NULL;
	}
}

/* Remove the backend area in xenbus since the framebuffer really is
   going away. */
void xenfb_shutdown(struct xenfb *xenfb)
{
	fprintf(stderr, "FB: Shutting down backend\n");
	xs_rm(xenfb->xsh, XBT_NULL, xenfb->fb.nodename);
	xs_rm(xenfb->xsh, XBT_NULL, xenfb->kbd.nodename);

	xenfb_detach_dom(xenfb);
	if (xenfb->xc >= 0)
		xc_interface_close(xenfb->xc);
	if (xenfb->evt_xch >= 0)
		xc_evtchn_close(xenfb->evt_xch);
	if (xenfb->xsh)
		xs_daemon_close(xenfb->xsh);
	free(xenfb);
}

static int xenfb_configure_fb(struct xenfb *xenfb,
			      int width, int height, int depth,
			      size_t fb_len, int row_stride)
{
	size_t mfn_sz = sizeof(*((struct xenfb_page *)0)->pd);
	size_t pd_len = sizeof(((struct xenfb_page *)0)->pd) / mfn_sz;
	size_t fb_pages = pd_len * XC_PAGE_SIZE / mfn_sz;
	size_t fb_len_lim = fb_pages * XC_PAGE_SIZE;
	int max_width, max_height;

	if (fb_len > fb_len_lim) {
		fprintf(stderr,
			"FB: frontend fb size %zu limited to %zu\n",
			fb_len, fb_len_lim);
		fb_len = fb_len_lim;
	}
	if (depth != 8 && depth != 16 && depth != 24 && depth != 32) {
		fprintf(stderr,
			"FB: can't handle frontend fb depth %d\n",
			depth);
		return -1;
	}
	if (row_stride < 0 || row_stride > fb_len) {
		fprintf(stderr,
			"FB: invalid frontend stride %d\n", row_stride);
		return -1;
	}
	max_width = row_stride / (depth / 8);
	if (width < 0 || width > max_width) {
		fprintf(stderr,
			"FB: invalid frontend width %d limited to %d\n",
			width, max_width);
		width = max_width;
	}
	max_height = fb_len / row_stride;
	if (height < 0 || height > max_height) {
		fprintf(stderr,
			"FB: invalid frontend height %d limited to %d\n",
			height, max_height);
		height = max_height;
	}
	xenfb->fb_len = fb_len;
	xenfb->row_stride = row_stride;
	xenfb->depth = depth;
	xenfb->width = width;
	xenfb->height = height;
	fprintf(stderr, "Framebuffer %dx%dx%d stride %d\n",
		width, height, depth, row_stride);
	return 0;
}

static void xenfb_on_fb_event(struct xenfb *xenfb)
{
	uint32_t prod, cons;
	struct xenfb_page *page = xenfb->fb.page;

	prod = page->out_prod;
	if (prod == page->out_cons)
		return;
	rmb();			/* ensure we see ring contents up to prod */
	for (cons = page->out_cons; cons != prod; cons++) {
		union xenfb_out_event *event = &XENFB_OUT_RING_REF(page, cons);
		int x, y, w, h;

		switch (event->type) {
		case XENFB_TYPE_UPDATE:
			x = MAX(event->update.x, 0);
			y = MAX(event->update.y, 0);
			w = MIN(event->update.width, xenfb->width - x);
			h = MIN(event->update.height, xenfb->height - y);
			if (w < 0 || h < 0) {
				fprintf(stderr, "%s bogus update ignored\n",
					xenfb->fb.nodename);
				break;
			}
			if (x != event->update.x || y != event->update.y
			    || w != event->update.width
			    || h != event->update.height) {
				fprintf(stderr, "%s bogus update clipped\n",
					xenfb->fb.nodename);
			}
			xenfb_guest_copy(xenfb, x, y, w, h);
			break;
		}
	}
	mb();			/* ensure we're done with ring contents */
	page->out_cons = cons;
	xc_evtchn_notify(xenfb->evt_xch, xenfb->fb.port);
}

static void xenfb_on_kbd_event(struct xenfb *xenfb)
{
	struct xenkbd_page *page = xenfb->kbd.page;

	/* We don't understand any keyboard events, so just ignore them. */
	if (page->out_prod == page->out_cons)
		return;
	page->out_cons = page->out_prod;
	xc_evtchn_notify(xenfb->evt_xch, xenfb->kbd.port);
}

static int xenfb_on_state_change(struct xenfb_device *dev)
{
	enum xenbus_state state;

	state = xenfb_read_state(dev->xenfb->xsh, dev->otherend);

	switch (state) {
	case XenbusStateUnknown:
		/* There was an error reading the frontend state.  The
		   domain has probably gone away; in any case, there's
		   not much point in us continuing. */
		return -1;
	case XenbusStateInitialising:
	case XenbusStateInitWait:
	case XenbusStateInitialised:
	case XenbusStateConnected:
		break;
	case XenbusStateClosing:
		xenfb_unbind(dev);
		xenfb_switch_state(dev, state);
		break;
	case XenbusStateClosed:
		xenfb_switch_state(dev, state);
	}
	return 0;
}

/* Send an event to the keyboard frontend driver */
static int xenfb_kbd_event(struct xenfb *xenfb,
			   union xenkbd_in_event *event)
{
	uint32_t prod;
	struct xenkbd_page *page = xenfb->kbd.page;

	if (xenfb->kbd.state != XenbusStateConnected)
		return 0;

	prod = page->in_prod;
	if (prod - page->in_cons == XENKBD_IN_RING_LEN) {
		errno = EAGAIN;
		return -1;
	}

	mb();			/* ensure ring space available */
	XENKBD_IN_RING_REF(page, prod) = *event;
	wmb();			/* ensure ring contents visible */
	page->in_prod = prod + 1;
	return xc_evtchn_notify(xenfb->evt_xch, xenfb->kbd.port);
}

/* Send a keyboard (or mouse button) event */
static int xenfb_send_key(struct xenfb *xenfb, bool down, int keycode)
{
	union xenkbd_in_event event;

	memset(&event, 0, XENKBD_IN_EVENT_SIZE);
	event.type = XENKBD_TYPE_KEY;
	event.key.pressed = down ? 1 : 0;
	event.key.keycode = keycode;

	return xenfb_kbd_event(xenfb, &event);
}

/* Send a relative mouse movement event */
static int xenfb_send_motion(struct xenfb *xenfb, int rel_x, int rel_y, int rel_z)
{
	union xenkbd_in_event event;

	memset(&event, 0, XENKBD_IN_EVENT_SIZE);
	event.type = XENKBD_TYPE_MOTION;
	event.motion.rel_x = rel_x;
	event.motion.rel_y = rel_y;
	event.motion.rel_z = rel_z;

	return xenfb_kbd_event(xenfb, &event);
}

/* Send an absolute mouse movement event */
static int xenfb_send_position(struct xenfb *xenfb, int abs_x, int abs_y, int abs_z)
{
	union xenkbd_in_event event;

	memset(&event, 0, XENKBD_IN_EVENT_SIZE);
	event.type = XENKBD_TYPE_POS;
	event.pos.abs_x = abs_x;
	event.pos.abs_y = abs_y;
	event.pos.abs_z = abs_z;

	return xenfb_kbd_event(xenfb, &event);
}

/* Process events from the frontend event channel */
static void xenfb_dispatch_channel(void *opaque)
{
	struct xenfb *xenfb = (struct xenfb *)opaque;
	evtchn_port_t port;
	port = xc_evtchn_pending(xenfb->evt_xch);
	if (port == -1) {
		xenfb_shutdown(xenfb);
		exit(1);
	}

	if (port == xenfb->fb.port)
		xenfb_on_fb_event(xenfb);
	else if (port == xenfb->kbd.port)
		xenfb_on_kbd_event(xenfb);

	if (xc_evtchn_unmask(xenfb->evt_xch, port) == -1) {
		xenfb_shutdown(xenfb);
		exit(1);
	}
}

/* Process ongoing events from the frontend devices */
static void xenfb_dispatch_store(void *opaque)
{
	struct xenfb *xenfb = (struct xenfb *)opaque;
	unsigned dummy;
	char **vec;
	int r;

	vec = xs_read_watch(xenfb->xsh, &dummy);
	free(vec);
	r = xenfb_on_state_change(&xenfb->fb);
	if (r == 0)
		r = xenfb_on_state_change(&xenfb->kbd);
	if (r < 0) {
		xenfb_shutdown(xenfb);
		exit(1);
	}
}


/****************************************************************
 *
 * Functions for processing frontend config
 *
 ****************************************************************/


/* Process the frontend framebuffer config */
static int xenfb_read_frontend_fb_config(struct xenfb *xenfb) {
	struct xenfb_page *fb_page;
	int val;

        if (xenfb_xs_scanf1(xenfb->xsh, xenfb->fb.otherend, "feature-update",
                            "%d", &val) < 0)
                val = 0;
        if (!val) {
                fprintf(stderr, "feature-update not supported\n");
                errno = ENOTSUP;
                return -1;
        }
        if (xenfb_xs_scanf1(xenfb->xsh, xenfb->fb.otherend, "protocol", "%63s",
                            xenfb->protocol) < 0)
                xenfb->protocol[0] = '\0';
        xenfb_xs_printf(xenfb->xsh, xenfb->fb.nodename, "request-update", "1");

	fb_page = xenfb->fb.page;
	if (xenfb_configure_fb(xenfb,
			       fb_page->width, fb_page->height, fb_page->depth,
			       fb_page->mem_length, fb_page->line_length)
	    < 0) {
		errno = EINVAL;
		return -1;
	}

        fprintf(stderr, "Framebuffer depth %d width %d height %d line %d\n",
                fb_page->depth, fb_page->width, fb_page->height, fb_page->line_length);
        if (xenfb_map_fb(xenfb, xenfb->fb.otherend_id) < 0)
		return -1;

        if (xenfb_switch_state(&xenfb->fb, XenbusStateConnected))
                return -1;
        if (xenfb_switch_state(&xenfb->kbd, XenbusStateConnected))
                return -1;

	return 0;
}

/* Process the frontend keyboard config */
static int xenfb_read_frontend_kbd_config(struct xenfb *xenfb)
{
	int val;

	if (xenfb_xs_scanf1(xenfb->xsh, xenfb->kbd.otherend, "request-abs-pointer",
			    "%d", &val) < 0)
		val = 0;
	xenfb->abs_pointer_wanted = val;

	return 0;
}


/****************************************************************
 *
 * Functions for frontend/backend state machine
 *
 ****************************************************************/

/* Register a watch against a frontend device, and setup
 * QEMU event loop to poll the xenstore FD for notification */
static int xenfb_wait_for_frontend(struct xenfb_device *dev, IOHandler *handler)
{
        fprintf(stderr, "Doing frontend watch on %s\n", dev->otherend);
	if (!xs_watch(dev->xenfb->xsh, dev->otherend, "")) {
		fprintf(stderr, "Watch for dev failed\n");
		return -1;
	}

	if (qemu_set_fd_handler2(xs_fileno(dev->xenfb->xsh), NULL, handler, NULL, dev) < 0)
		return -1;

	return 0;
}

/* Register a watch against a backend device, and setup
 * QEMU event loop to poll the xenstore FD for notification */
static int xenfb_wait_for_backend(struct xenfb_device *dev, IOHandler *handler)
{
	fprintf(stderr, "Doing backend watch on %s\n", dev->nodename);
	if (!xs_watch(dev->xenfb->xsh, dev->nodename, "")) {
		fprintf(stderr, "Watch for dev failed\n");
		return -1;
	}

	if (qemu_set_fd_handler2(xs_fileno(dev->xenfb->xsh), NULL, handler, NULL, dev) < 0)
		return -1;

	return 0;
}

/* Callback invoked while waiting for KBD backend to change
 * to the created state */
static void xenfb_backend_created_kbd(void *opaque)
{
	struct xenfb_device *dev = (struct xenfb_device *)opaque;
	int ret = xenfb_backend_created(dev);
	if (ret < 0) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}
	if (ret)
		return; /* Still waiting */

	if (xenfb_xs_printf(dev->xenfb->xsh, dev->nodename, "feature-abs-pointer", "1")) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}

	fprintf(stderr, "FB: Waiting for FB backend creation\n");
	xenfb_wait_for_backend(&dev->xenfb->fb, xenfb_backend_created_fb);
}

/* Callback invoked while waiting for FB backend to change
 * to the created state */
static void xenfb_backend_created_fb(void *opaque)
{
	struct xenfb_device *dev = (struct xenfb_device *)opaque;
	int ret = xenfb_backend_created(dev);
	if (ret < 0) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}
	if (ret)
		return; /* Still waiting */

	fprintf(stderr, "FB: Waiting for KBD frontend initialization\n");
	xenfb_wait_for_frontend(&dev->xenfb->kbd, xenfb_frontend_initialized_kbd);
}

/* Callback invoked while waiting for KBD frontend to change
 * to the initialized state */
static void xenfb_frontend_initialized_kbd(void *opaque)
{
	struct xenfb_device *dev = (struct xenfb_device *)opaque;
	int ret = xenfb_frontend_initialized(dev);
	if (ret < 0) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}
	if (ret)
		return; /* Still waiting */


        fprintf(stderr, "FB: Waiting for FB frontend initialization\n");
	xenfb_wait_for_frontend(&dev->xenfb->fb, xenfb_frontend_initialized_fb);
}

/* Callback invoked while waiting for FB frontend to change
 * to the initialized state */
static void xenfb_frontend_initialized_fb(void *opaque)
{
	struct xenfb_device *dev = (struct xenfb_device *)opaque;
	int ret = xenfb_frontend_initialized(dev);
	if (ret < 0) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}
	if (ret)
		return; /* Still waiting */


	if (xenfb_read_frontend_fb_config(dev->xenfb)) {
		xenfb_shutdown(dev->xenfb);
	        exit(1);
	}

        fprintf(stderr, "FB: Waiting for KBD frontend connection\n");
	xenfb_wait_for_frontend(&dev->xenfb->kbd, xenfb_frontend_connected_kbd);
}

/* Callback invoked while waiting for KBD frontend to change
 * to the connected state */
static void xenfb_frontend_connected_kbd(void *opaque)
{
	struct xenfb_device *dev = (struct xenfb_device *)opaque;
	int ret = xenfb_frontend_connected(dev);
	if (ret < 0) {
		xenfb_shutdown(dev->xenfb);
		exit(1);
	}
	if (ret)
		return; /* Still waiting */

	if (xenfb_read_frontend_kbd_config(dev->xenfb) < 0) {
		xenfb_shutdown(dev->xenfb);
	        exit(1);
	}

	xenfb_register_console(dev->xenfb);
}


/****************************************************************
 *
 * Helper functions for checking state of frontend/backend devices
 *
 ****************************************************************/

/* Helper to determine if a frontend device is in Connected state */
static int xenfb_frontend_connected(struct xenfb_device *dev)
{
	unsigned int state;
	unsigned int dummy;
	char **vec;
	vec = xs_read_watch(dev->xenfb->xsh, &dummy);
	if (!vec)
		return -1;
	free(vec);

	state = xenfb_read_state(dev->xenfb->xsh, dev->otherend);
	if (!((1 <<state) & ((1 << XenbusStateUnknown) |
			     (1 << XenbusStateConnected)))) {
		fprintf(stderr, "FB: Carry on waiting\n");
		return 1;
	}

	/* Don't unwatch frontend - we need to detect shutdown */
	/*xs_unwatch(dev->xenfb->xsh, dev->otherend, "");*/

	switch (state) {
	case XenbusStateConnected:
		break;
	default:
		return -1;
	}
	return 0;
}


/* Helper to determine if a frontend device is in Initialized state */
static int xenfb_frontend_initialized(struct xenfb_device *dev)
{
	unsigned int state;
	unsigned int dummy;
	char **vec;
	vec = xs_read_watch(dev->xenfb->xsh, &dummy);
	if (!vec)
		return -1;
	free(vec);

	state = xenfb_read_state(dev->xenfb->xsh, dev->otherend);

	if (!((1 << state) & ((1 << XenbusStateUnknown)
			      | (1 << XenbusStateInitialised)
#if 1 /* TODO fudging state to permit restarting; to be removed */
			      | (1 << XenbusStateConnected)
#endif
			      ))) {
		fprintf(stderr, "FB: Carry on waiting\n");
		return 1;
	}

	xs_unwatch(dev->xenfb->xsh, dev->otherend, "");

	switch (state) {
#if 1
	case XenbusStateConnected:
                printf("Fudging state to %d\n", XenbusStateInitialised); /* FIXME */
#endif
        case XenbusStateInitialised:
                break;
        default:
                return -1;
        }

	if (xenfb_bind(dev) < 0)
		return -1;

	return 0;
}

/* Helper to determine if a backend device is in Created state */
static int xenfb_backend_created(struct xenfb_device *dev)
{
	unsigned int state;
	unsigned int dummy;
	char **vec;
	vec = xs_read_watch(dev->xenfb->xsh, &dummy);
	if (!vec)
		return -1;
	free(vec);

	state = xenfb_read_state(dev->xenfb->xsh, dev->nodename);

	if (!((1 <<state) & ((1 << XenbusStateUnknown)
			     | (1 << XenbusStateInitialising)
			     | (1 << XenbusStateClosed)
#if 1 /* TODO fudging state to permit restarting; to be removed */
			     | (1 << XenbusStateInitWait)
			     | (1 << XenbusStateConnected)
			     | (1 << XenbusStateClosing)
#endif
			     ))) {
		fprintf(stderr, "FB: Carry on waiting\n");
		return 1;
	}

	xs_unwatch(dev->xenfb->xsh, dev->nodename, "");

        switch (state) {
#if 1
        case XenbusStateInitWait:
        case XenbusStateConnected:
                printf("Fudging state to %d\n", XenbusStateInitialising); /* FIXME */
#endif
        case XenbusStateInitialising:
        case XenbusStateClosing:
        case XenbusStateClosed:
                break;
        default:
                fprintf(stderr, "Wrong state %d\n", state);
                return -1;
        }
        xenfb_switch_state(dev, XenbusStateInitWait);
        if (xenfb_hotplug(dev) < 0)
                return -1;

        return 0;
}


/****************************************************************
 * 
 * QEMU device model integration functions
 *
 ****************************************************************/

/* 
 * Send a key event from the client to the guest OS
 * QEMU gives us a raw scancode from an AT / PS/2 style keyboard.
 * We have to turn this into a Linux Input layer keycode.
 * 
 * Extra complexity from the fact that with extended scancodes 
 * (like those produced by arrow keys) this method gets called
 * twice, but we only want to send a single event. So we have to
 * track the '0xe0' scancode state & collapse the extended keys
 * as needed.
 * 
 * Wish we could just send scancodes straight to the guest which
 * already has code for dealing with this...
 */
static void xenfb_key_event(void *opaque, int scancode)
{
    static int extended = 0;
    int down = 1;
    if (scancode == 0xe0) {
        extended = 1;
        return;
    } else if (scancode & 0x80) {
        scancode &= 0x7f;
        down = 0;
    }
    if (extended) {
        scancode |= 0x80;
        extended = 0;
    }
    xenfb_send_key(opaque, down, scancode2linux[scancode]);
}

/*
 * Send a mouse event from the client to the guest OS
 * 
 * The QEMU mouse can be in either relative, or absolute mode.
 * Movement is sent separately from button state, which has to
 * be encoded as virtual key events. We also don't actually get
 * given any button up/down events, so have to track changes in
 * the button state.
 */
static void xenfb_mouse_event(void *opaque,
			      int dx, int dy, int dz, int button_state)
{
    int i;
    struct xenfb *xenfb = opaque;
    if (xenfb->abs_pointer_wanted)
	    xenfb_send_position(xenfb,
                                dx * (xenfb->ds->width - 1) / 0x7fff,
                                dy * (xenfb->ds->height - 1) / 0x7fff,
				dz);
    else
	    xenfb_send_motion(xenfb, dx, dy, dz);

    for (i = 0 ; i < 8 ; i++) {
	    int lastDown = xenfb->button_state & (1 << i);
	    int down = button_state & (1 << i);
	    if (down == lastDown)
		    continue;

	    if (xenfb_send_key(xenfb, down, BTN_LEFT+i) < 0)
		    return;
    }
    xenfb->button_state = button_state;
}

/* A convenient function for munging pixels between different depths */
#define BLT(SRC_T,DST_T,RLS,GLS,BLS,RRS,GRS,BRS,RM,GM,BM)               \
    for (line = y ; line < h ; line++) {                                \
        SRC_T *src = (SRC_T *)(xenfb->pixels                            \
                               + (line * xenfb->row_stride)             \
                               + (x * xenfb->depth / 8));               \
        DST_T *dst = (DST_T *)(xenfb->ds->data                                 \
                               + (line * xenfb->ds->linesize)                  \
                               + (x * xenfb->ds->depth / 8));                  \
        int col;                                                        \
        for (col = x ; col < w ; col++) {                               \
            *dst = (((*src >> RRS) & RM) << RLS) |                      \
                (((*src >> GRS) & GM) << GLS) |                         \
                (((*src >> GRS) & BM) << BLS);                          \
            src++;                                                      \
            dst++;                                                      \
        }                                                               \
    }


/* This copies data from the guest framebuffer region, into QEMU's copy
 * NB. QEMU's copy is stored in the pixel format of a) the local X 
 * server (SDL case) or b) the current VNC client pixel format.
 * When shifting between colour depths we preserve the MSB.
 */
static void xenfb_guest_copy(struct xenfb *xenfb, int x, int y, int w, int h)
{
    int line;

    if (xenfb->depth == xenfb->ds->depth) { /* Perfect match can use fast path */
        for (line = y ; line < (y+h) ; line++) {
            memcpy(xenfb->ds->data + (line * xenfb->ds->linesize) + (x * xenfb->ds->depth / 8),
                   xenfb->pixels + (line * xenfb->row_stride) + (x * xenfb->depth / 8),
                   w * xenfb->depth / 8);
        }
    } else { /* Mismatch requires slow pixel munging */
        if (xenfb->depth == 8) {
            /* 8 bit source == r:3 g:3 b:2 */
            if (xenfb->ds->depth == 16) {
                BLT(uint8_t, uint16_t,   5, 2, 0,   11, 5, 0,   7, 7, 3);
            } else if (xenfb->ds->depth == 32) {
                BLT(uint8_t, uint32_t,   5, 2, 0,   16, 8, 0,   7, 7, 3);
            }
        } else if (xenfb->depth == 16) {
            /* 16 bit source == r:5 g:6 b:5 */
            if (xenfb->ds->depth == 8) {
                BLT(uint16_t, uint8_t,    11, 5, 0,   5, 2, 0,    31, 63, 31);
            } else if (xenfb->ds->depth == 32) {
                BLT(uint16_t, uint32_t,   11, 5, 0,   16, 8, 0,   31, 63, 31);
            }
        } else if (xenfb->depth == 32) {
            /* 32 bit source == r:8 g:8 b:8 (padding:8) */
            if (xenfb->ds->depth == 8) {
                BLT(uint32_t, uint8_t,    16, 8, 0,   5, 2, 0,    255, 255, 255);
            } else if (xenfb->ds->depth == 16) {
                BLT(uint32_t, uint16_t,   16, 8, 0,   11, 5, 0,   255, 255, 255);
            }
        }
    }
    dpy_update(xenfb->ds, x, y, w, h);
}

/* QEMU display state changed, so refresh the framebuffer copy */
/* XXX - can we optimize this, or the next func at all ? */ 
static void xenfb_update(void *opaque)
{
    struct xenfb *xenfb = opaque;
    xenfb_guest_copy(xenfb, 0, 0, xenfb->width, xenfb->height);
}

/* QEMU display state changed, so refresh the framebuffer copy */
static void xenfb_invalidate(void *opaque)
{
    struct xenfb *xenfb = opaque;
    xenfb_guest_copy(xenfb, 0, 0, xenfb->width, xenfb->height);
}

/* Screen dump is not used in Xen, so no need to impl this....yet */
static void xenfb_screen_dump(void *opaque, const char *name) { }


/* Register a QEMU graphical console, and key/mouse handler,
 * connecting up their events to the frontend */
static int xenfb_register_console(struct xenfb *xenfb) {
	/* Register our keyboard & mouse handlers */
	qemu_add_kbd_event_handler(xenfb_key_event, xenfb);
	qemu_add_mouse_event_handler(xenfb_mouse_event, xenfb,
  				     xenfb->abs_pointer_wanted,
  				     "Xen PVFB Mouse");
  
  	/* Tell QEMU to allocate a graphical console */
	graphic_console_init(xenfb->ds,
			     xenfb_update,
			     xenfb_invalidate,
			     xenfb_screen_dump,
			     xenfb);
	dpy_resize(xenfb->ds, xenfb->width, xenfb->height);

	if (qemu_set_fd_handler2(xc_evtchn_fd(xenfb->evt_xch), NULL, xenfb_dispatch_channel, NULL, xenfb) < 0)
	        return -1;
	if (qemu_set_fd_handler2(xs_fileno(xenfb->xsh), NULL, xenfb_dispatch_store, NULL, xenfb) < 0)
		return -1;

        fprintf(stderr, "Xen Framebuffer registered\n");
        return 0;
}

/*
 * Local variables:
 *  c-indent-level: 8
 *  c-basic-offset: 8
 *  tab-width: 8
 * End:
 */

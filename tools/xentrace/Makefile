XEN_ROOT=../..
include $(XEN_ROOT)/tools/Rules.mk

CFLAGS  += -Werror

CFLAGS  += -I $(XEN_XC)
CFLAGS  += -I $(XEN_LIBXC)

HDRS     = $(wildcard *.h)
OBJS     = $(patsubst %.c,%.o,$(wildcard *.c))

BIN      = xentrace xentrace_setsize
LIBBIN   = 
SCRIPTS  = xentrace_format
MAN1     = $(wildcard *.1)
MAN8     = $(wildcard *.8)

ifeq ($(XEN_TARGET_ARCH),x86_32)
LIBBIN  += xenctx
endif

ifeq ($(XEN_TARGET_ARCH),x86_64)
LIBBIN  += xenctx
endif

ifeq ($(XEN_TARGET_ARCH),ia64)
LIBBIN  += xenctx
endif

.PHONY: all
all: build

.PHONY: build
build: $(BIN) $(LIBBIN)

.PHONY: install
install: build
	[ -d $(DESTDIR)/usr/bin ] || $(INSTALL_DIR) $(DESTDIR)/usr/bin
	[ -z "$(LIBBIN)" ] || [ -d $(DESTDIR)/usr/$(LIBDIR)/xen/bin ] || \
		$(INSTALL_DIR) $(DESTDIR)/usr/$(LIBDIR)/xen/bin
	[ -d $(DESTDIR)/usr/share/man/man1 ] || \
		$(INSTALL_DIR) $(DESTDIR)/usr/share/man/man1
	[ -d $(DESTDIR)/usr/share/man/man8 ] || \
		$(INSTALL_DIR) $(DESTDIR)/usr/share/man/man8
	$(INSTALL_PROG) $(BIN) $(SCRIPTS) $(DESTDIR)/usr/bin
	[ -z "$(LIBBIN)" ] || $(INSTALL_PROG) $(LIBBIN) $(DESTDIR)/usr/$(LIBDIR)/xen/bin
	$(INSTALL_DATA) $(MAN1) $(DESTDIR)/usr/share/man/man1
	$(INSTALL_DATA) $(MAN8) $(DESTDIR)/usr/share/man/man8

.PHONY: clean
clean:
	$(RM) *.a *.so *.o *.rpm $(BIN) $(LIBBIN)

%: %.c $(HDRS) Makefile
	$(CC) $(CFLAGS) -o $@ $< -L$(XEN_LIBXC) -lxenctrl
xentrace_%: %.c $(HDRS) Makefile
	$(CC) $(CFLAGS) -o $@ $< -L$(XEN_LIBXC) -lxenctrl

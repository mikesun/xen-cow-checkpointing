
override XEN_TARGET_ARCH = x86_32
XEN_ROOT = ../../../..
CFLAGS :=
include $(XEN_ROOT)/tools/Rules.mk

SOURCES = util.c
TARGET = 32bitbios_flat.h

CFLAGS += -fno-builtin -O2 -msoft-float -nostdlib
CFLAGS += -I../ -DGCC_PROTOS
CFLAGS += $(call cc-option,$(CC),-fno-stack-protector,)
CFLAGS += $(call cc-option,$(CC),-fno-stack-protector-all,)

SUBDIRS = tcgbios

MODULES = tcgbios/tcgbiosext.o

.PHONY: all subdirs clean

subdirs:
	@set -e; for subdir in $(SUBDIRS); do \
		$(MAKE) -C $$subdir all; \
	done;

all: $(TARGET)

clean:
	rm -rf *.o $(TARGET)
	@for subdir in $(SUBDIRS); do \
		$(MAKE) -C $$subdir $@; \
	done;

$(TARGET): subdirs 32bitbios.o util.o
	$(LD) $(LDFLAGS_DIRECT) -s -r 32bitbios.o $(MODULES) util.o -o 32bitbios_all.o
	@nm 32bitbios_all.o |                                \
	  egrep '^ +U ' >/dev/null && {                      \
	    echo "There are undefined symbols in the BIOS:"; \
	    nm -u 32bitbios_all.o;                           \
	    exit 11;                                         \
	  } || :
	sh mkhex highbios_array 32bitbios_all.o > $@

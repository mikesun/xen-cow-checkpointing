XEN_ROOT=../../..
include $(XEN_ROOT)/tools/Rules.mk

CFLAGS  += -Werror

HDRS     = $(wildcard *.h)
OBJS     = $(patsubst %.c,%.o,$(wildcard *.c))

BIN      = lomount

.PHONY: all
all: build

.PHONY: build
build: $(BIN)

.PHONY: install
install: build
	$(INSTALL_PROG) $(BIN) $(SCRIPTS) $(DESTDIR)/usr/bin

.PHONY: clean
clean:
	$(RM) *.a *.so *.o *.rpm $(BIN)

%: %.c $(HDRS) Makefile
	$(CC) $(CFLAGS) -o $@ $< 


#CONFIG += -DNDEBUG     # disable debugging and asserts
CONFIG += -DNVALGRIND   # remove Valgrind markup
#CONFIG += -DNJIT       # disable machine code generation (AMD64 only)
#CONFIG += -DNSHORTCUT  # remove shortcut paths (reduce code size)

OBJECTS = main.o value.o alloc.o parse.o func.o code.o error.o apply.o \
                 verb.o adverb.o arith.o string.o sys.o
HEADERS =        value.h alloc.h parse.h func.h code.h error.h apply.h \
                 verb.h adverb.h arith.h string.h sys.h tree.h
TARGET  = kuc

CC      = gcc
CFLAGS  = -ggdb -O3 -march=native -std=gnu99 -fms-extensions \
          -I/usr/local/include \
          -Wall -Wno-parentheses -Wno-attributes -Wpointer-arith
LDFLAGS = -L/usr/local/lib -lm -ledit -ltermcap

$(TARGET): $(OBJECTS) Makefile
	$(CC) -o $@ $(OBJECTS) $(LDFLAGS)

$(OBJECTS): $(HEADERS) Makefile
.c.o:
	$(CC) $(CONFIG) $(CFLAGS) -c $<

.PHONY: clean
clean:
	rm -f -- $(OBJECTS) $(TARGET)

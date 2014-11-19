#include "alloc.h"

void write_char(unsigned char *buf, unsigned char val) {
    *buf = val;
}

void write_chars(unsigned char *buf, unsigned char val, unsigned int n) {
    unsigned int i;
    for (i = 0; i < n; i++)
        *(buf + i) = val;
}

void write_char_unsafe(void *buf, int val) {
    unsigned char *dest = buf;
    *dest = (unsigned char) val;
}

void write_chars_unsafe(void *buf, unsigned char val, unsigned int n) {
    unsigned char *dest = buf;
    unsigned int i;
    for (i = 0; i < n; i++)
        *(dest + i) = val;
}

extern struct heap *h;
extern struct mem_node *start;

#define HEAP_START 0x100000

void test_func(void) {
    init_allocator(h, start);
    unsigned int *buf = alloc(h, 12, 0);
    write_chars_unsafe(buf, 0x9c, 12);
}

void write_char_wrong(void *buf, int val) {
    unsigned char *dest = buf;
    *(dest + 1) = (unsigned char) val;
}

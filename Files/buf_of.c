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

#define TPM_SHA1_160_HASH_LEN    0x14

typedef struct tdTPM_DIGEST
{
    unsigned char digest[TPM_SHA1_160_HASH_LEN];
} TPM_DIGEST;

/*
void test_func(void) {
    init_allocator(h, start);
    unsigned int *buf = alloc(h, sizeof(TPM_DIGEST), 0);
    write_chars_unsafe(buf, 0x9c, 12);
}
*/

TPM_DIGEST dig;

void test_func(void) {
    write_chars_unsafe(&dig, 0x9c, 12);
}

void test_func_WRONG(void) {
    write_chars_unsafe(&dig, 0x9c, 50);
}

void write_char_wrong(void *buf, int val) {
    unsigned char *dest = buf;
    *(dest + 1) = (unsigned char) val;
}

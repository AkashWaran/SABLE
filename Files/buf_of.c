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

void write_char_wrong(void *buf, int val) {
    unsigned char *dest = buf;
    *(dest + 1) = (unsigned char) val;
}

void fill_buf(void *buf, unsigned int length, int val) {
    unsigned char *dest = buf;
    unsigned int i;
    for (i = 0; i < length; i++) {
	dest[i] = (unsigned char) val;
    }
}

void fill_buf_WRONG(void *buf, unsigned int length, int val) {
    unsigned char *dest = buf;
    unsigned int i;
    for (i = 0; i <= length; i++) {
	dest[i] = (unsigned char) val;
    }
}

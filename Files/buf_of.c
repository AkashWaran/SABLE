void write_char(void *buf, int val) {
    unsigned char *dest = buf;
    *dest = (unsigned char) val;
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

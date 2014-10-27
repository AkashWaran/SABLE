void write_char(void *buf) {
    unsigned char *ch = buf;
    *ch = 0x48;
}

void fill_buf(void *buf, unsigned int length) {
    unsigned char *b = buf;
    unsigned int i;
    for (i = 0; i < length; i++) {
	b[i] = 0x69;
    }
}

void fill_buf_WRONG(void *buf, unsigned int length) {
    unsigned char *b = buf;
    unsigned int i;
    for (i = 0; i <= length; i++) {
	b[i] = 0x69;
    }
}

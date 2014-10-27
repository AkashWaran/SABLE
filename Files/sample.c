void writeBuffer(char *buf, unsigned int length) {
    int i;
    for (i = 0; i < length; i++) {
	buf[i] = 0x69;
    }
}

void writeBuffer_WRONG(char *buf, unsigned int length) {
    int i;
    for (i = 0; i < length + 1; i++) {
	buf[i] = 0x69;
    }
}

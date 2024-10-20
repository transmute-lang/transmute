
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

void stdout_write(const void *buf, uintptr_t count) {
    char *string = malloc(count + 1);
    memcpy(string, buf, count);
    string[count] = 0;
    fputs(string, stdout);
    free(string);
}

void stdout_flush(void) {
    fflush(stdout);
}
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "llvm.h"

LlvmStackFrame *gc_root = 0;

LlvmStackFrame *get_llvm_gc_root_chain(void) {
    return gc_root;
}

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
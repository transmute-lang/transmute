// main-pre.c
#include <stdbool.h>

// we want to use the inlined header
#define GC_H_INLINE
#define GC_PRIVATE

static Args args = {0};
static void *frames = NULL;

Args *get_c_args(void) {
    return &args;
}


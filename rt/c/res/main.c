#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "gc.h"

// todo rename f to some order name that makes sense in transmute source
int64_t f(int64_t n);

int main(int argc, char **argv) {
    gc_init();

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <N>\n", argv[0]);
        return 1;
    }

    int64_t n = strtoll(argv[1], NULL, 10);

    for (int64_t i = 0; i < n; i++) {
        printf("f(%li) = %li\n", i, f(i));
    }

#ifdef GC_TEST
    gc_pool_dump();
    gc_print_statistics();
#endif

    return 0;
}

void print(int64_t a) {
    printf("%li\n", a);
}

void assert_ptr_eq(void *a, void *b) {
    assert(a == b);
}

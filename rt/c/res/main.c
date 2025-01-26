#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "gc.h"

// main(number) -> _TM0_4main1n
int64_t _TM0_4main1n(int64_t n);

int main(int argc, char **argv) {
    gc_init();

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <N>\n", argv[0]);
        return 1;
    }

    int64_t n = strtoll(argv[1], NULL, 10);

    for (int64_t i = 0; i < n; i++) {
        printf("main(%li) = %li\n", i, _TM0_4main1n(i));
    }

    gc_teardown();

    return 0;
}

// print(number) -> _TM0_5print1n
void _TM0_5print1n(int64_t a) {
    printf("%li\n", a);
}

// print(boolean) -> _TM0_5print1b
void _TM0_5print1b(int8_t b) {
    if (b) {
        printf("true\n");
    } else {
        printf("false\n");
    }
}

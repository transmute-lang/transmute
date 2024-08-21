#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>

int64_t f(int64_t n);

int main(int argc, char** argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <N>\n", argv[0]);
        return 1;
    }

    int64_t n = strtoll(argv[1], NULL, 10);

    for (int64_t i = 0; i < n; i++) {
        printf("f(%li) = %li\n", i, f(i));
    }
}

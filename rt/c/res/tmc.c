#include <stdio.h>
#include <stdlib.h>

void tmc_check_array_index(size_t i, size_t len, size_t line, size_t column) {
    if (i < 0 || i >= len) {
        // todo:ux add file path and reformat as "error at file:line:column" when we have it
        fprintf(stderr, "error at line %lu, column %lu\n", line, column);
        fprintf(stderr, "index out of bounds: the len is %lu but the index is %lu\n", len, i);
        exit(1);
    }
}
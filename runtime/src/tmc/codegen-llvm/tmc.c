#include <stdio.h>
#include <stdlib.h>

void tmc_check_array_index(size_t i, size_t length, size_t line, size_t column) {
    if (i < 0 || i >= length) {
        // todo:ux add file path and reformat as "error at file:line:column" when we have it
        fprintf(stderr, "error at line %lu, column %lu\n", line, column);
        fprintf(stderr, "index out of bounds: the length is %lu but the index is %lu\n", length, i);
        exit(1);
    }
}
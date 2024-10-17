
#include <stdint.h>
#include <stdio.h>

void println(const char *str) {
    printf("%s\n", str);
}

void print_alloc(uintptr_t size, uintptr_t align) {
    printf("alloc: %lu, %lu\n", size, align);
}

void print_dealloc(uintptr_t size, uintptr_t align) {
    printf("dealloc: %lu, %lu\n", size, align);
}
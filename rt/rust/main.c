
#include <stdio.h>
#include <string.h>
#include "bindings/rustrt.h"
#include "../c/res/gc.h"

void rust_malloc(uintptr_t size, uintptr_t align) {
    printf("Rust wants %lu bytes aligned to %lu\n", size, align);
}
void rust_dealloc(const uint8_t *ptr, uintptr_t size, uintptr_t align) {
    printf("Rust wants to dealloc %lu bytes aligned to %lu, starting at %p\n", size, align, ptr);
}

int main(int argc, char **argv)
{
    gc_init();

    printf("sizeof(Str)=%lu\n", sizeof(Str));

    Str *str = str_new_cstr("Hello, world!");

    printf("str=%p\n", str);
    printf("str->inner=%s\n", str->inner);
    printf("str->len=%lu\n", str->len);

    gc_teardown();
    return 0;
}
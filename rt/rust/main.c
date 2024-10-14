
#include <stdio.h>
#include "bindings/rustrt.h"

void println(const char *str) {
    printf("%s\n", str);
}

int main() {
//    gc_init();

    println("new_struct_with_string_as_box()");
    MyStructWithString *s1 = new_struct_with_string_as_box();

    println("print_struct_with_string_as_box(s1)");
    print_struct_with_string_as_box(s1);
    println("print_struct_with_string_as_ref(s1)");
    print_struct_with_string_as_ref(s1);

    println("free_struct_with_string_as_box(s1)");
    free_struct_with_string_as_box(s1);

    println("new_struct_with_string_as_ptr()");
    void *s2 = new_struct_with_string_as_ptr();

    println("print_struct_with_string_as_ptr(s1)");
    print_struct_with_string_as_ptr(s2);

    println("free_struct_with_string_as_ptr(s2)");
    free_struct_with_string_as_ptr(s2);

    println("");

    println("new_struct_with_str_as_box()");
    MyStructWithStr *s3 = new_struct_with_str_as_box();

    println("get_str_from_struct_with_str_as_ref(s3)");
    const Str *str = get_str_from_struct_with_str_as_ref(s3);

    printf("str = '");
    for (int i = 0; i < str->len; i++) {
        printf("%c", str->ptr[i]);
    }
    printf("'; len=%lu; cap=%lu\n", str->len, str->cap);

    println("free_str_as_box(str)");
    free_str_as_box(str);

    println("free_struct_with_str_as_box(s3)");
    free_struct_with_str_as_box(s3);
}
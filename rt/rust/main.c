
#include <stdio.h>
#include "bindings/rustrt.h"

int main() {
//    gc_init();

    printf("gc_list_blocks() - 1\n");
    gc_list_blocks();
    printf("\n");

    printf("new_struct_with_string_as_box()\n");
    MyStructWithString *s1 = new_struct_with_string_as_box();
    printf("\n");

    printf("gc_list_blocks() - 2\n");
    gc_list_blocks();
    printf("\n");

    printf("print_struct_with_string_as_box(s1)\n");
    print_struct_with_string_as_box(s1);
    printf("\n");
    printf("print_struct_with_string_as_ref(s1)\n");
    print_struct_with_string_as_ref(s1);
    printf("\n");

    printf("free_struct_with_string_as_box(s1)\n");
    free_struct_with_string_as_box(s1);
    printf("\n");

    printf("gc_list_blocks() - 3\n");
    gc_list_blocks();
    printf("\n");

    printf("new_struct_with_string_as_ptr()\n");
    void *s2 = new_struct_with_string_as_ptr();
    printf("\n");

    printf("gc_list_blocks() - 4\n");
    gc_list_blocks();
    printf("\n");

    printf("print_struct_with_string_as_ptr(s1)\n");
    print_struct_with_string_as_ptr(s2);
    printf("\n");

    printf("free_struct_with_string_as_ptr(s2)\n");
    free_struct_with_string_as_ptr(s2);
    printf("\n");

    printf("new_struct_with_str_as_box()\n");
    MyStructWithStr *s3 = new_struct_with_str_as_box();
    printf("\n");

    printf("get_str_from_struct_with_str_as_ref(s3)\n");
    Str *str = get_str_from_struct_with_str_as_ref(s3);
    printf("\n");

    printf("str = '");
    for (int i = 0; i < str->len; i++) {
        printf("%c", str->ptr[i]);
    }
    printf("'; len=%lu; cap=%lu\n", str->len, str->cap);
    printf("\n");

    printf("is_managed_str_as_box(str)\n");
    is_managed_str_as_box(str);
    printf("\n");

    printf("is_managed_str_as_ref(str)\n");
    is_managed_str_as_ref(str);
    printf("\n");

    printf("is_managed_str_as_ptr(str)\n");
    is_managed_str_as_ptr(str);
    printf("\n");

    printf("is_managed_str_as_void_ptr(str)\n");
    is_managed_str_as_void_ptr(str);
    printf("\n");

    printf("free_struct_with_str_as_box(s3)\n");
    free_struct_with_str_as_box(s3);
    printf("\n");

    printf("gc_list_blocks() - end\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_alloc(1, 1)\n");
    void *block1 = gc_alloc(1, 1);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_alloc(2, 1)\n");
    void *block2 = gc_alloc(2, 1);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_free(block1)\n");
    gc_free(block1);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_alloc(3, 1)\n");
    void *block3 = gc_alloc(3, 1);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_free(block3)\n");
    gc_free(block3);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");

    printf("gc_free(block2)\n");
    gc_free(block2);
    printf("\n");

    printf("gc_list_blocks()\n");
    gc_list_blocks();
    printf("\n");
}
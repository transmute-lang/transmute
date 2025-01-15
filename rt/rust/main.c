
#include <stdio.h>
#include "bindings/rustrt.h"

extern LlvmStackFrame *gc_root;

int main() {
    Str *str1 = stdlib_string_new();
    Str *str2 = stdlib_string_new();
    Str *str3 = stdlib_string_new();
    List *list = stdlib_list_new();
    List *lists1 = gc_alloc(2, 16);
    List *lists2 = gc_alloc(2, 16);

    printf("str1 = %p\n", str1);
    printf("str2 = %p\n", str2);
    printf("str3 = %p\n", str3);
    printf("list = %p\n", list);
    printf("lists1 = %p\n", lists1);
    printf("lists2 = %p\n", lists2);

    #define NUM_ROOTS 3
    gc_root = malloc(sizeof(LlvmStackFrame) + NUM_ROOTS * sizeof(void *));
    gc_root->map = malloc(sizeof(LlvmFrameMap));
    gc_root->map->num_roots = NUM_ROOTS;
    gc_root->next = 0;
    gc_root->roots[0] = list;
    gc_root->roots[1] = str2;
    gc_root->roots[2] = lists1;

    gc_disable();
    for (int i = 0; i < 16; i++) {
        printf("list=%p, list.ptr=%p, list.len=%lu, list.cap=%lu\n", list, list->ptr, list->len, list->cap);
        stdlib_list_push(list, str1);
    }
    gc_enable();

    printf("test:expect-live:%p\n", (void *)list);
    printf("test:expect-live:%p\n", (void *)list->ptr);
    printf("test:expect-live:%p\n", (void *)str1);
    printf("test:expect-live:%p\n", (void *)str1->ptr);
    printf("test:expect-live:%p\n", (void *)str2);
    printf("test:expect-live:%p\n", (void *)str2->ptr);
    printf("test:expect-live:%p\n", (void *)lists1);

    printf("\ngc_collect()\n");
    gc_collect();

    printf("\ngc_list_blocks()\n");
    gc_list_blocks();

    const void *object_ptr = gc_next_object_ptr(NULL);
    while (object_ptr != NULL) {
        printf("test:actual-live:%p\n", object_ptr);
        object_ptr = gc_next_object_ptr(object_ptr);
    }
}
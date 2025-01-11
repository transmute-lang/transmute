
#include <stdio.h>
#include "bindings/rustrt.h"

extern LlvmStackFrame *gc_root;

int main() {
    Str *str0 = new_string();
    Str *str1 = new_string();

    printf("test:expect-free:%p\n", (void *)str0);
    printf("test:expect-free:%p\n", (void *)str0->ptr);
    printf("test:expect-live:%p\n", (void *)str1);
    printf("test:expect-live:%p\n", (void *)str1->ptr);

    gc_root = malloc(sizeof(LlvmStackFrame));
    gc_root->map = malloc(sizeof(LlvmFrameMap));
    gc_root->map->num_roots = 1;
    gc_root->next = 0;
    gc_root->roots = str1;

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
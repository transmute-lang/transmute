
#include <stdio.h>
#include <string.h>
#include "llvm.h"
#include "bindings/rustrt.h"

extern LlvmStackFrame *gc_root;

int main() {
    Str *str1 = stdlib_string_new();
    Str *str2 = stdlib_string_new();
    Str *str3 = stdlib_string_new();
    List *list = stdlib_list_new();
    List *lists1 = gc_malloc(2, 16);
    List *lists2 = gc_malloc(2, 16);

    printf("str1 = %p\n", str1);
    printf("str2 = %p\n", str2);
    printf("str3 = %p\n", str3);
    printf("list = %p\n", list);
    printf("lists1 = %p\n", lists1);
    printf("lists2 = %p\n", lists2);

    #define NUM_ROOTS 4
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

    printf("\ngc_run()\n");
    gc_run();

    printf("<remaining blocks>\n");
    gc_list_blocks();
    printf("</remaining blocks>\n");

    const void *object_ptr = gc_next_object_ptr(NULL);
    while (object_ptr != NULL) {
        printf("test:actual-live:%p\n", object_ptr);
        object_ptr = gc_next_object_ptr(object_ptr);
    }

//    void *http_client = stdlib_http_client_new();
//    gc_root->roots[3] = http_client;

//    Str *str4 = stdlib_http_client_get(http_client);
//    char *c_str = malloc(str4->len + 1);
//    memcpy(c_str, str4->ptr, str4->len);
//    c_str[str4->len] = 0;

//    gc_root->map->num_roots = NUM_ROOTS - 1;
//    gc_run();
    //stdlib_http_client_free(http_client);

//    printf("str4 = %s\n", c_str);
}
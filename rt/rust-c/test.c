
#include <stdio.h>
#include <string.h>
#include "gc.h"
#include "llvm.h"
#include "bindings/rust.h"

extern LlvmStackFrame *llvm_gc_root_chain;

void array3_mark(void *object) {
    void **array3 = object;
    for (int i = 0; i < 3; i++) {
        if (array3[i]) {
            gc_mark(array3[i]);
        }
    }
}

void array3_free(void *object) {
    // nothing
}

GcCallbacks array3_callbacks = {
    .mark = array3_mark,
    .free = array3_free
};

int main() {
    #define NUM_ROOTS   5
    #define IDX_ARRAY1  0
    #define IDX_LIST    1
    #define IDX_MAP     2
    #define IDX_ARRAY2  3
    llvm_gc_root_chain = malloc(sizeof(LlvmStackFrame) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map = malloc(sizeof(LlvmFrameMap) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map->num_roots = NUM_ROOTS;
    llvm_gc_root_chain->map->num_meta = 0;
    llvm_gc_root_chain->next = 0;

    printf("\n--- gc_init -------------------+\n");
    gc_init();

    gc_pool_dump();

    printf("\n--- gc_malloc() ---------------+\n");
    void **array3 = gc_malloc(3 * sizeof(void *), 1, &array3_callbacks);
    gc_set_object_name(array3, "array3");
    memset(array3, 0, 3 * sizeof(void *));
    llvm_gc_root_chain->roots[IDX_ARRAY1] = array3;

    gc_pool_dump();

    printf("\n--- stdlib_string_new ----------+\n");
    Str *str = stdlib_string_new();
    gc_set_object_name(str, "str");
    printf("str = %p\n", (void *)str);

    gc_pool_dump();

    printf("\n--- array3[0] = str -----------+\n");
    array3[0] = str;

    printf("\n--- stdlib_list_new() ---------+\n");
    List *list = stdlib_list_new();
    gc_set_object_name(list, "list");
    llvm_gc_root_chain->roots[IDX_LIST] = list;
    printf("list at %p has len=%li, cap=%li\n", (void *)list, list->len, list->cap);

    gc_pool_dump();

    printf("\n--- stdlib_list_push(str) -----+\n");
    stdlib_list_push(list, str);
    array3[0] = 0;

    gc_pool_dump();

    printf("\n--- stdlib_map_new() ----------+\n");
    Map *map = stdlib_map_new();
    gc_set_object_name(map, "map");
    llvm_gc_root_chain->roots[IDX_MAP] = map;
    printf("map = %p\n", (void *)map);

    gc_pool_dump();

    printf("\n--- gc_malloc() ---------------+\n");
    void **ptr = gc_malloc(3 * sizeof(void *), 1, &array3_callbacks);
    gc_set_object_name(ptr, "ptr");
    memset(ptr, 0, 3 * sizeof(void *));
    llvm_gc_root_chain->roots[IDX_ARRAY2] = ptr;

    printf("\n--- stdlib_map_insert() -------+\n");
//    fprintf(stderr, "handle hashing\n"); return 1;
    stdlib_map_insert(map, str, ptr);
    llvm_gc_root_chain->roots[IDX_ARRAY2] = 0;

    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- stdlib_list_pop() ---------+\n");
    stdlib_list_pop(list);
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- stdlib_map_remove() -------+\n");
    stdlib_map_remove(map, str);
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- unroot array3 -------------+\n");
    llvm_gc_root_chain->roots[IDX_ARRAY1] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- unroot list ---------------+\n");
    llvm_gc_root_chain->roots[IDX_LIST] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- unroot map ---------------+\n");
    llvm_gc_root_chain->roots[IDX_MAP] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();

    printf("\n--- gc_teardown ---------------+\n");
    gc_teardown();
}

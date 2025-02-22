#include <stdio.h>
#include <string.h>
#include <assert.h>
#include "../src/gc/gc.h"
#include "../../stdlib/bindings/transmute-stdlib.h"

#define __LLVM_DEFINE_ROOT
#include "../src/llvm/llvm.h"

// extern LlvmStackFrame *llvm_gc_root_chain;

void array3_mark(void *object) {
    void **array3 = object;
    for (int i = 0; i < 3; i++) {
        if (array3[i]) {
            gc_mark(array3[i]);
        }
    }
}

GcCallbacks array3_callbacks = {
    .mark = array3_mark,
    .free = NULL
};

#define PAUSE() do { if (step) { getchar(); } } while(false)

int main() {
    bool step = false;
    char *env_step = getenv("GC_TEST_STEP");
    if (env_step && strcmp(env_step, "1") == 0) {
        step = true;
    }

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
    PAUSE();

    printf("\n--- gc_malloc(array3) ---------+\n");
    void **array3 = gc_malloc(3 * sizeof(void *), 1, &array3_callbacks);
    gc_set_object_name(array3, "array3");
    memset(array3, 0, 3 * sizeof(void *));
    llvm_gc_root_chain->roots[IDX_ARRAY1] = array3;
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_string_new ----------+\n");
    Str *str = stdlib_string_new();
    gc_set_object_name(str, "str");
    printf("str = %p\n", (void *)str);
    gc_pool_dump();
    PAUSE();

    printf("\n--- array3[0] = str -----------+\n");
    array3[0] = str;
    PAUSE();

    printf("\n--- stdlib_list_new() ---------+\n");
    List *list = stdlib_list_new();
    gc_set_object_name(list, "list");
    llvm_gc_root_chain->roots[IDX_LIST] = list;
    printf("list at %p has len=%li, cap=%li\n", (void *)list, list->len, list->cap);
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_list_push(str) -----+\n");
    stdlib_list_push(list, str);
    array3[0] = 0;
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_map_new() ----------+\n");
    Map *map = stdlib_map_new();
    gc_set_object_name(map, "map");
    llvm_gc_root_chain->roots[IDX_MAP] = map;
    printf("map = %p\n", (void *)map);
    gc_pool_dump();
    PAUSE();

    printf("\n--- gc_malloc(ptr) ------------+\n");
    void **ptr = gc_malloc(3 * sizeof(void *), 1, &array3_callbacks);
    gc_set_object_name(ptr, "ptr");
    memset(ptr, 0, 3 * sizeof(void *));
    llvm_gc_root_chain->roots[IDX_ARRAY2] = ptr;
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_map_insert() -------+\n");
    MapKey map_key = {
        .value = str,
        .vtable = &STDLIB_STR_MAPKEY_VTABLE,
    };
    MapValue prev = stdlib_map_insert(map, map_key, ptr);
    assert(prev == NULL);
    llvm_gc_root_chain->roots[IDX_ARRAY2] = 0;
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_map_len() ----------+\n");
    printf("stdlib_map_len() = %li\n", stdlib_map_len(map));
    assert(stdlib_map_len(map) == 1);
    gc_pool_dump();
    PAUSE();

    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_list_pop() ---------+\n");
    stdlib_list_pop(list);
    PAUSE();

    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- stdlib_map_get() ----------+\n");
    MapValue val = stdlib_map_get(map, map_key);
    printf("val=%p ptr=%p\n", (void *)val, (void *)ptr);
    assert(val == ptr);
    PAUSE();

    printf("\n--- stdlib_map_remove() -------+\n");
    MapValue rem = stdlib_map_remove(map, map_key);
    printf("rem=%p ptr=%p\n", (void *)rem, (void *)ptr);
    assert(rem == ptr);
    PAUSE();

    printf("\n--- stdlib_map_len() ----------+\n");
    printf("stdlib_map_len() = %li\n", stdlib_map_len(map));
    assert(stdlib_map_len(map) == 0);
    PAUSE();

    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- unroot array3 -------------+\n");
    llvm_gc_root_chain->roots[IDX_ARRAY1] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- unroot list ---------------+\n");
    llvm_gc_root_chain->roots[IDX_LIST] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- unroot map ---------------+\n");
    llvm_gc_root_chain->roots[IDX_MAP] = 0;
    printf("\n--- gc_run() ------------------+\n");
    gc_run();
    gc_pool_dump();
    PAUSE();

    printf("\n--- gc_teardown ---------------+\n");
    gc_teardown();
    PAUSE();
}

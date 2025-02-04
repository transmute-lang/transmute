
#include <stdio.h>
#include "gc.h"
#include "llvm.h"
#include "bindings/rust.h"

extern LlvmStackFrame *llvm_gc_root_chain;

int main() {
//    printf("sizeof(GcBlockState) = %li\n", sizeof(GcBlockState));               // 4
//    printf("sizeof(GcBlock) = %li\n", sizeof(GcBlock));                         // 24
//    printf("sizeof(LlvmStackFrame) = %li\n", sizeof(LlvmStackFrame));           // 16
//    printf("sizeof(LlvmFrameMap) = %li\n", sizeof(LlvmFrameMap));               // 8
//    printf("sizeof(GcStructField) = %li\n", sizeof(GcStructField));             // 16
//    printf("sizeof(GcArrayElement) = %li\n", sizeof(GcArrayElement));           // 8
//    printf("sizeof(GcPointeeKind) = %li\n", sizeof(GcPointeeKind));             // 8
//    printf("sizeof(GcPointeeKindTag) = %li\n", sizeof(GcPointeeKindTag));       // 4
//    printf("sizeof(GcPointeeLayout) = %li\n", sizeof(GcPointeeLayout));         // 24

    GcPointeeLayout *managed_meta = malloc(sizeof(GcPointeeLayout));
    managed_meta->tag = Managed;
    managed_meta->count = 0;

    GcPointeeLayout *array_meta = malloc(sizeof(GcPointeeLayout));
    array_meta->tag = Array;
    array_meta->count = 0;

    #define NUM_ROOTS   5
    #define IDX_LIST    0
    #define IDX_STR     1
    #define IDX_ELEMENT 2
    #define IDX_PTR     3
    #define IDX_MAP     4
    llvm_gc_root_chain = malloc(sizeof(LlvmStackFrame) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map = malloc(sizeof(LlvmFrameMap) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map->num_roots = NUM_ROOTS;
    llvm_gc_root_chain->map->num_meta = NUM_ROOTS;
    llvm_gc_root_chain->next = 0;

    printf("\n--- gc_init -------------------+\n");
    gc_init();

    gc_pool_dump();

    printf("\n--- stdlib_string_new ----------+\n");
    Str *str = stdlib_string_new();
    llvm_gc_root_chain->map->meta[IDX_STR] = managed_meta;
    llvm_gc_root_chain->roots[IDX_STR] = str;

    printf("str = %p\n", (void *)str);

    gc_pool_dump();

    printf("\n--- stdlib_list_new -----------+\n");
    List *list = stdlib_list_new();
    llvm_gc_root_chain->map->meta[IDX_LIST] = managed_meta;
    llvm_gc_root_chain->roots[IDX_LIST] = list;

    printf("list at %p has len=%li, cap=%li\n", (void *)list, list->len, list->cap);

    gc_pool_dump();

    printf("\n--- gc_malloc(69, 1)-----------+\n");
    void *element = gc_malloc(69, 1, NULL);
    llvm_gc_root_chain->map->meta[IDX_ELEMENT] = array_meta;
    llvm_gc_root_chain->roots[IDX_ELEMENT] = element;

    gc_pool_dump();

    printf("\n--- stdlib_list_push(str) -----+\n");
    stdlib_list_push(list, str);
    llvm_gc_root_chain->map->meta[IDX_STR] = 0;
    llvm_gc_root_chain->roots[IDX_STR] = 0;

    gc_pool_dump();

    printf("\n--- stdlib_list_push(element) -+\n");
    stdlib_list_push(list, element);
    llvm_gc_root_chain->map->meta[IDX_ELEMENT] = 0;
    llvm_gc_root_chain->roots[IDX_ELEMENT] = 0;

    gc_pool_dump();

    printf("\n--- gc_malloc(2, 1) -----------+\n");
    char *ptr = gc_malloc(2, 1, NULL);
    ptr[0] = 'B';
    ptr[1] = 'B';
    llvm_gc_root_chain->map->meta[IDX_PTR] = managed_meta;
    llvm_gc_root_chain->roots[IDX_PTR] = ptr;

    gc_pool_dump();

    printf("\n--- stdlib_map_new() ----------+\n");
    Map *map = stdlib_map_new();
    llvm_gc_root_chain->map->meta[IDX_MAP] = managed_meta;
    llvm_gc_root_chain->roots[IDX_MAP] = map;

    printf("map = %p\n", (void *)map);

    gc_pool_dump();

    printf("\n--- stdlib_map_push() ---------+\n");
    stdlib_map_push(map, str, ptr);

    llvm_gc_root_chain->map->meta[IDX_LIST] =0;
    llvm_gc_root_chain->roots[IDX_LIST] = 0;
    llvm_gc_root_chain->map->meta[IDX_PTR] = 0;
    llvm_gc_root_chain->roots[IDX_PTR] = 0;
//    llvm_gc_root_chain->map->meta[IDX_MAP] = 0;
//    llvm_gc_root_chain->roots[IDX_MAP] = 0;

    gc_pool_dump();

    printf("\n--- gc_run --------------------+\n");
    gc_run();

    gc_pool_dump();

    printf("\n--- gc_teardown ---------------+\n");
    gc_teardown();
}


#include <stdio.h>
#include "gc.h"
#include "llvm.h"
#include "bindings/rust.h"

extern LlvmStackFrame *llvm_gc_root_chain;

// see GcAlloc::alloc()
#define OBJECT(object) (*(void **)( (char *)object - sizeof(void *)))

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

    #define NUM_ROOTS 4
    llvm_gc_root_chain = malloc(sizeof(LlvmStackFrame) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map = malloc(sizeof(LlvmFrameMap) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map->num_roots = NUM_ROOTS;
    llvm_gc_root_chain->map->num_meta = NUM_ROOTS;
    llvm_gc_root_chain->next = 0;

    printf("\n--- gc_init -------------------+\n");
    gc_init();

    printf("\n--- stdlib_string_new ----------+\n");
    Str *str = stdlib_string_new();
    llvm_gc_root_chain->map->meta[2] = managed_meta;
    llvm_gc_root_chain->roots[2] = OBJECT(str);

    printf("str = %p\n", (void *)str);

    printf("\n--- stdlib_list_new -----------+\n");
    List *list = stdlib_list_new();
    llvm_gc_root_chain->map->meta[0] = managed_meta;
    llvm_gc_root_chain->roots[0] = OBJECT(list);

    printf("list at %p has len=%li, cap=%li\n", (void *)list, list->len, list->cap);

    printf("\n--- gc_malloc(69, 1)-----------+\n");
    void *element = gc_malloc(69, 1);
    llvm_gc_root_chain->map->meta[1] = array_meta;
    llvm_gc_root_chain->roots[1] = element;

    printf("\n--- stdlib_list_push(str) -----+\n");
    stdlib_list_push(list, str);

    printf("\n--- stdlib_list_push(element) -+\n");
    stdlib_list_push(list, element);

    llvm_gc_root_chain->map->meta[1] = 0;
    llvm_gc_root_chain->roots[1] = 0;
    llvm_gc_root_chain->map->meta[2] = 0;
    llvm_gc_root_chain->roots[2] = 0;

    printf("\n--- gc_malloc(2, 1)------------+\n");
    char *ptr = gc_malloc(2, 1);
    ptr[0] = 'B';
    ptr[1] = 'B';

    printf("\n--- gc_run --------------------+\n");
    gc_run();

    gc_pool_dump();

    printf("\n--- gc_teardown ---------------+\n");
    gc_teardown();
}

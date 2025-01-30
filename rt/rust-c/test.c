
#include <stdio.h>
#include "gc.h"
#include "llvm.h"
#include "bindings/rust.h"

extern LlvmStackFrame *llvm_gc_root_chain;

//typedef enum GcBlockState {
//    Unreachable = 0,
//    Reachable   = 1,
//    Owned       = 2,
//} GcBlockState;
//typedef struct GcBlock {        // 24 bytes
//    GcBlockState     state;     //  8 (4 + 4)
//    struct GcBlock  *next;      //  8
//    size_t           data_size; //  8
//    uint8_t          data[];    //  0
//} GcBlock;

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

    #define NUM_ROOTS 4
    llvm_gc_root_chain = malloc(sizeof(LlvmStackFrame) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map = malloc(sizeof(LlvmFrameMap) + NUM_ROOTS * sizeof(void *));
    llvm_gc_root_chain->map->num_roots = NUM_ROOTS;
    llvm_gc_root_chain->map->num_meta = NUM_ROOTS;
    llvm_gc_root_chain->next = 0;

    gc_init();

    Str *str = stdlib_string_new();
    printf("str1 = %p\n", (void *)str);

    GcPointeeLayout *meta = malloc(sizeof(GcPointeeLayout));
    meta->tag = Managed;
    meta->count = 1;

    llvm_gc_root_chain->map->meta[0] = meta;

    // see GcAlloc::alloc()
    void *object = *(void **)( (char *)str - sizeof(void *));

    llvm_gc_root_chain->roots[0] = object;

    gc_run();

    gc_teardown();
}

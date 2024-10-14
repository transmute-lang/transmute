#include <stdio.h>
#include <string.h>
#include "bindings/rustrt.h"
#include "../c/res/gc.h"

typedef struct LlvmFrameMap {
    int32_t      num_roots;
    int32_t      num_meta;
    const void  *meta[2];
} LlvmFrameMap;

typedef struct LlvmStackFrame {
    struct LlvmStackFrame *next;
    const  LlvmFrameMap   *map;
    void                  *roots[2];
} LlvmStackFrame;

LlvmStackFrame *llvm_gc_root_chain;

void rust_print(const char *what) {
    printf("Rust says: %s\n", what);
}

void gc_run();

static char* init = "Hello, world!_";
static size_t layout_opaque[2] = { 2, 0 };

int main(int argc, char **argv) {
    // printf("sizeof(Str)=%lu\n", sizeof(Str));

    gc_init();

    LlvmFrameMap map = {
        .num_roots = 2,
        .num_meta = 2,
        .meta = { layout_opaque, layout_opaque },
    };
    LlvmStackFrame frame = {
        .next =  llvm_gc_root_chain,
        .map = &map,
        .roots = { NULL, NULL }
    };
    llvm_gc_root_chain = &frame;
//
//    char *cstr = (void *)gc_malloc(strlen(init) + 1, 1, true);
//    llvm_gc_root_chain->roots[0] = cstr;
//
//    memcpy(cstr, init, strlen(init) + 1);
//
//    cstr[13] = 0;
//    Str *str = str_new_cstr(cstr);
//    cstr[13] = '_';
//
//    llvm_gc_root_chain->roots[1] = str;
//    str_println(str);
//    gc_run();
//    gc_print_statistics();
//
//    llvm_gc_root_chain->roots[1] = NULL;
//    gc_run();
//    gc_print_statistics();

    Outer *outer = outer_new();
//    llvm_gc_root_chain->roots[0] = outer;
//    printf("** addr outer: %p\n", outer);

//    str_println(&outer->inner.string);

//gc_run();

//    printf("** before: str_new_static\n");
    Str *str = str_new_static((uint8_t *)init, strlen(init), strlen(init));
//    printf("** addr str: %p\n", str);

//    llvm_gc_root_chain->roots[1] = str;

//    outer_add(outer, str, 42);

//    printf("str object: %p\n", str);
//    printf("str->inner object: %p\n", str->inner);
//    gc_print_statistics();

    gc_teardown();
    return 0;
}
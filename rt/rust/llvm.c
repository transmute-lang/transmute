#include <stdint.h>
#include "llvm.h"

LlvmStackFrame *gc_root = 0;

LlvmStackFrame *get_llvm_gc_root_chain(void) {
    return gc_root;
}
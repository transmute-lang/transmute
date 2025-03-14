#include <stdint.h>

typedef struct LlvmFrameMap {
    int32_t      num_roots;
    int32_t      num_meta;
    void        *meta[];
} LlvmFrameMap;

typedef struct LlvmStackFrame {
    struct LlvmStackFrame *next;
    LlvmFrameMap          *map;
    void                  *roots[];
} LlvmStackFrame;

#ifdef __LLVM_DEFINE_ROOT
LlvmStackFrame *llvm_gc_root_chain;
#endif // __LLVM_DEFINE_ROOT

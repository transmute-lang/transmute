#include <stdint.h>

typedef struct LlvmFrameMap {
    int32_t      num_roots;
    int32_t      num_meta;
    void        *meta[0];
} LlvmFrameMap;

typedef struct LlvmStackFrame {
    struct LlvmStackFrame *next;
    LlvmFrameMap          *map;
    void                  *roots[0];
} LlvmStackFrame;
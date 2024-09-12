// LLVM Ref.: https://llvm.org/docs/GarbageCollection.html#id15

// The map for a single function's stack frame.
//
// One of these is compiled as constant data into the executable for each function.
// Storage of metadata values is elided if the `%metadata` parameter to  `@llvm.gcroot` is null.
typedef struct LlvmFrameMap {
    int32_t      num_roots;       // number of roots in stack frame.
    int32_t      num_meta;        // number of metadata entries.
    const void  *meta[0];         // metadata for each root.
} LlvmFrameMap;

// A link in the dynamic shadow stack.
//
// One of these is embedded in the stack frame of each function on the call  stack.
typedef struct LlvmStackFrame {
    struct LlvmStackFrame *next;      // link to next stack entry (the caller's).
    const  LlvmFrameMap   *map;       // pointer to constant FrameMap.
    void                  *roots[0];  // stack roots (in-place array).
} LlvmStackFrame;

LlvmStackFrame *llvm_gc_root_chain;
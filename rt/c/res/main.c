#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

// todo rename f to some order name that makes sense in transmute source
int64_t f(int64_t n);

void gc_init();
void gc_pool_dump();

int main(int argc, char **argv) {
    gc_init();

    if (argc < 2) {
        fprintf(stderr, "Usage: %s <N>\n", argv[0]);
        return 1;
    }

    int64_t n = strtoll(argv[1], NULL, 10);

    for (int64_t i = 0; i < n; i++) {
        printf("f(%li) = %li\n", i, f(i));
    }

#ifdef GC_TEST
    gc_pool_dump();
#endif

    return 0;
}

void print(int64_t a) {
    printf("%li\n", a);
}

void assert_ptr_eq(void *a, void *b) {
    assert(a == b);
}

///////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
// GC stuff
//
// LLVM Ref.: https://llvm.org/docs/GarbageCollection.html#id15

// defines:
//  - GC_TEST: compile with test mode support
//
// standard env. variables
//  - GC_ENABLE: if set to 0, GC is not executed
//
// test mode env. variables
//  - GC_TEST_DUMP:       if set to 1, a memory dump is printed to stdout at the end of program execution
//  - GC_TEST_DUMP_COLOR: if set to 1, the memory dump is colored
//  - GC_TEST_VERBOSE:    if set to 1, print GC messages; if set to 2, print more GC messages, etc.

#ifdef GC_TEST
#define BOUNDARY   0xBB
#define FREE       0xFF
#define ALLOCATED  0xAA
#define FREED      0xDD
#define POOL_SIZE  1024
#define POOL_START 65536

uint8_t *pool = NULL;
uint8_t *pool_free = NULL;
int gc_log_level = 0;
int gc_test_dump = 0;
int gc_test_dump_color = 0;
#endif

int gc_enable = 1;

typedef enum BlockState {
    Unreachable = 0,
    Reachable   = 1
} BlockState;

static inline char* state_to_char(BlockState state) {
    switch (state) {
        case Unreachable: return "unreachable";
        case Reachable: return "reachable";
        default: assert(0);
    }
}

typedef struct Block {
    BlockState     state;
    struct Block  *next;
    size_t         data_size;
    uint8_t        data[];
} Block;

static Block *blocks_chain = NULL;

#ifdef GC_TEST
static Block *freed_blocks_chain = NULL;
#endif

static inline void gc_log(int level, const char *fmt, ...) {
#ifdef GC_TEST
    if (gc_log_level >= level) {
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
#endif
}

static inline void ident(int level, int depth) {
#ifdef GC_TEST
    if (gc_log_level >= level) {
        for (int i = 0; i < depth; i++) {
            printf("  ");
        }
    }
#endif
}

void block_print(Block *block) {
    gc_log(2, "  block at %p (object of size %li at %p): %s\n",
        block,
        block->data_size,
        (void *)block + sizeof(Block),
        state_to_char(block->state)
    );
}

// The map for a single function's stack frame.
//
// One of these is compiled as constant data into the executable for each function.
// Storage of metadata values is elided if the `%metadata` parameter to  `@llvm.gcroot` is null.
typedef struct FrameMap {
    int32_t      num_roots;       // number of roots in stack frame.
    int32_t      num_meta;        // number of metadata entries.
    const void  *meta[0];         // metadata for each root.
} FrameMap;

// A link in the dynamic shadow stack.
//
// One of these is embedded in the stack frame of each function on the call  stack.
typedef struct StackFrame {
    struct StackFrame *next;      // link to next stack entry (the caller's).
    const  FrameMap   *map;       // pointer to constant FrameMap.
    void              *roots[0];  // stack roots (in-place array).
} StackFrame;

typedef int64_t Meta;

StackFrame *llvm_gc_root_chain;

void gc_mark_visitor(int depth, void *object, const Meta *meta) {
    Block *block = object - sizeof(Block);

    ident(2, depth);
    gc_log(2, "      object at %p (block at %p): %li pointers, %s\n",
        object,
        block,
        meta[0],
        state_to_char(block->state)
    );

    if (block->state == Reachable) {
        return;
    }
    block->state = Reachable;

    ident(3, depth);
    gc_log(3, "      (cnt) meta[0]=%li\n", meta[0]);
    for (int64_t i = 0; i < meta[0]; i++) {
        ident(3, depth);
        gc_log(3, "      (off) meta[%li]=%li\n", 1 + i*2, meta[1 + i*2]);
        ident(3, depth);
        gc_log(3, "      (met) meta[%li]=%p\n", 1 + i*2 + 1, (void *)meta[1 + i*2 + 1]);

        int64_t offset = meta[1 + i*2];
        void *child_offset = object + offset;
        void *child = (void *)*(int64_t *)child_offset;

        ident(2, depth);
        gc_log(2, "        %li. %p(+%li) -> %p\n", i, child_offset, offset, child);

        const Meta *child_meta = (Meta *)(void *)meta[1 + i*2 + 1];

        gc_mark_visitor(depth + 1, child, child_meta);
    }
}

void gc_free(Block *block) {
#ifdef GC_TEST
    gc_log(3, "memset %#02x at %p for %li bytes\n", FREED, block, sizeof(Block) + block->data_size);

    if (gc_test_dump_color) {
        // todo mutually exclusive: memset and coloring
        block->next = freed_blocks_chain;
        freed_blocks_chain = block;
    } else {
        memset((void *)block, FREED, sizeof(Block) + block->data_size);
    }

#else
    free(block);
#endif
}

#ifdef GC_TEST
void gc_pool_dump() {
    if (!gc_test_dump) {
        return;
    }

    printf("Memory dump:\n\n");
    for (size_t i = 0; i < POOL_SIZE; i++) {
        if (i == 0) {
            printf("    %p    ", &pool[i]);
        } else if (i % 16 == 0) {
           printf("\n    %p    ", &pool[i]);
        } else if (i % 4 == 0) {
            printf("  ");
        }

        if (gc_test_dump_color) {
            if (i < 2 * sizeof(int64_t) || i >= POOL_SIZE - 2 * sizeof(int64_t)) {
                printf("\033[31m%02x\033[0m ", pool[i]);
            } else if (i >= pool_free - pool) {
                printf("\033[34m%02x\033[0m ", pool[i]);
            } else {
                int freed = 0;
                void *byte_addr = &pool[i];
                Block *block = freed_blocks_chain;
                while (block) {
                    if (byte_addr >= block && byte_addr < (void *)(block + 1) + block->data_size) {
                        printf("\033[32m%02x\033[0m ", pool[i]);
                        freed = 1;
                        break;
                    }
                    block = block->next;
                }
                if (!freed) {
                    printf("%02x ", pool[i]);
                }
            }
        } else {
            printf("%02x ", pool[i]);
        }
    }
    printf("\n\n");
}
#endif

void gc() {
    if (!gc_enable) {
        return;
    }

    gc_log(2, "Start GC\n");

    Block *block = blocks_chain;
    while (block) {
        block->state = Unreachable;
        block_print(block);
        block = block->next;
    }

    StackFrame *frame = llvm_gc_root_chain;
    for (int i = 0; frame; i++) {
        // all roots have a meta associated
        assert(frame->map->num_roots == frame->map->num_meta);

        gc_log(2, "  frame %i", i);
        gc_log(3, " at %p", frame);
        gc_log(2, ":\n", i);

        for (int32_t i = 0; i < frame->map->num_roots; i++) {
            if (frame->roots[i]) {
                gc_log(2, "    root %i:\n", i);
                gc_mark_visitor(0, frame->roots[i], frame->map->meta[i]);
            } else {
                gc_log(2, "    root %i: skipped (nil)\n", i);
            }
        }

        frame = frame->next;
    }

    Block *prev = NULL;
    block = blocks_chain;
    while (block) {
        block_print(block);
        if (block->state == Unreachable) {
            if (block == blocks_chain) {
                blocks_chain = block->next;
            } else {
                assert(prev != NULL);
                prev->next = block->next;
            }
            Block *next = block->next;
            gc_log(1, "freeing block at %p (object size: %li)\n", block, block->data_size);
            gc_free(block);
            block = next;
        } else {
            prev = block;
            block = block->next;
        }
    }
}

void gc_init() {
#ifdef GC_TEST
    char *gc_enable_env = getenv("GC_ENABLE");
    if (gc_enable_env && strcmp(gc_enable_env, "0") == 0) {
        gc_enable = 0;
    }

    char *gc_test_log_env = getenv("GC_TEST_VERBOSE");
    if (gc_test_log_env) {
        gc_log_level = atoi(gc_test_log_env);
    }

    char *gc_test_dump_env = getenv("GC_TEST_DUMP");
    if (gc_test_dump_env && strcmp(gc_test_dump_env, "1") == 0) {
        gc_test_dump = 1;
    }

    char *gc_test_dump_color_env = getenv("GC_TEST_DUMP_COLOR");
    if (gc_test_dump_color_env && strcmp(gc_test_dump_color_env, "1") == 0) {
        gc_test_dump_color = 1;
    }

    gc_log(1, "Initialize GC with log level: %i\n", gc_log_level);

#include <sys/mman.h>
#include <errno.h>

    pool = mmap((void *)POOL_START, POOL_SIZE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS, -1, 0);
    gc_log(2, "Allocate test GC memory pool: mmap returned %p (%s)\n", pool, strerror(errno));
    assert(errno == 0);

    gc_log(3, "memset %#02x at %p for %i bytes\n", FREE, pool, POOL_SIZE);
    memset(pool, FREE, POOL_SIZE);
    memset(pool, BOUNDARY, 2 * sizeof(int64_t));
    memset(pool + POOL_SIZE - 2 * sizeof(int64_t), BOUNDARY, 2 * sizeof(int64_t));

    pool_free = pool + 2 * sizeof(int64_t);
#endif
}

void* gc_malloc(int64_t data_size) {
    gc();

    size_t alloc_size = sizeof(Block) + data_size;

#ifdef GC_TEST
    Block *block = (void *)pool_free;
    pool_free += alloc_size;
    gc_log(3, "memset %#02x at %p for %li bytes\n", ALLOCATED, block, alloc_size);
    memset(block, ALLOCATED, alloc_size);
#else
    Block *block = malloc(alloc_size);
#endif

    block->state = Unreachable;
    block->data_size = data_size;
    block->next = blocks_chain;
    blocks_chain = block;

    gc_log(1, "allocated block of size %li at %p, returning object of size %li at %p(+%li)\n",
        alloc_size,
        block,
        data_size,
        &block->data,
        (uint8_t *)block->data - (uint8_t *)block
    );

    return &block->data;
}
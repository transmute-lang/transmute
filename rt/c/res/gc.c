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

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "llvm.h"
#include "gc.h"

#ifdef GC_TEST
#define BOUNDARY   0xBB
#define FREE       0xFF
#define ALLOCATED  0xAA
#define FREED      0xDD
#define POOL_START 65536

#ifndef POOL_SIZE
#define POOL_SIZE  512
#endif // #ifndef POOL_SIZE
#endif // #ifdef GC_TEST

typedef enum GcBlockState {
    Unreachable = 0,
    Reachable   = 1
} GcBlockState;

static inline char* state_to_char(GcBlockState state) {
    switch (state) {
        case Unreachable: return "unreachable";
        case Reachable: return "reachable";
        default: assert(0);
    }
}

typedef struct GcBlock {
    GcBlockState     state;
    struct GcBlock  *next;
    size_t           data_size;
    uint8_t          data[];
} GcBlock;

typedef struct Gc {
    int enable;
    GcBlock *blocks_chain;
    #ifdef GC_TEST
    GcBlock *freed_blocks_chain;
    uint8_t *pool;
    uint8_t *pool_free;
    int log_level;
    int test_dump;
    int test_dump_color;
    #endif // #ifdef GC_TEST
} Gc;

typedef int64_t Meta;

Gc gc = {
    .enable = 1,
    .blocks_chain = NULL,
    #ifdef GC_TEST
    .freed_blocks_chain = NULL,
    .pool = NULL,
    .pool_free = NULL,
    .log_level = 0,
    .test_dump = 0,
    .test_dump_color = 0,
    #endif // #ifdef GC_TEST
};

void gc_run();

void* gc_malloc(int64_t data_size);
void gc_free(GcBlock *block);

static inline void gc_ident(int level, int depth);
static inline void gc_log(int level, const char *fmt, ...);
void gc_block_print(GcBlock *block);
void gc_mark_visitor(int depth, void *object, const Meta *meta);


static inline void gc_ident(int level, int depth) {
#ifdef GC_TEST
    if (gc.log_level >= level) {
        for (int i = 0; i < depth; i++) {
            printf("  ");
        }
    }
#endif
}

static inline void gc_log(int level, const char *fmt, ...) {
#ifdef GC_TEST
    if (gc.log_level >= level) {
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
#endif
}

void gc_block_print(GcBlock *block) {
    gc_log(2, "  block at %p (object of size %li at %p): %s\n",
        block,
        block->data_size,
        (void *)block + sizeof(GcBlock),
        state_to_char(block->state)
    );
}


#ifdef GC_TEST
void gc_pool_dump() {
    if (!gc.test_dump) {
        return;
    }

    printf("Memory dump:\n\n");
    for (size_t i = 0; i < POOL_SIZE; i++) {
        if (i == 0) {
            printf("    %p    ", &gc.pool[i]);
        } else if (i % 16 == 0) {
           printf("\n    %p    ", &gc.pool[i]);
        } else if (i % 4 == 0) {
            printf("  ");
        }

        if (gc.test_dump_color) {
            if (i < 2 * sizeof(int64_t) || i >= POOL_SIZE - 2 * sizeof(int64_t)) {
                printf("\033[31m%02x\033[0m ", gc.pool[i]);
            } else if (i >= gc.pool_free - gc.pool) {
                printf("\033[34m%02x\033[0m ", gc.pool[i]);
            } else {
                int freed = 0;
                void *byte_addr = &gc.pool[i];
                GcBlock *block = gc.freed_blocks_chain;
                while (block) {
                    if (byte_addr >= (void *)block && byte_addr < (void *)(block + 1) + block->data_size) {
                        printf("\033[32m%02x\033[0m ", gc.pool[i]);
                        freed = 1;
                        break;
                    }
                    block = block->next;
                }
                if (!freed) {
                    printf("%02x ", gc.pool[i]);
                }
            }
        } else {
            printf("%02x ", gc.pool[i]);
        }
    }
    printf("\n\n");
}
#endif // #ifdef GC_TEST

void gc_init() {
#ifdef GC_TEST
    char *gc_enable_env = getenv("GC_ENABLE");
    if (gc_enable_env && strcmp(gc_enable_env, "0") == 0) {
        gc.enable = 0;
    }

    char *gc_test_log_env = getenv("GC_TEST_VERBOSE");
    if (gc_test_log_env) {
        gc.log_level = atoi(gc_test_log_env);
    }

    char *gc_test_dump_env = getenv("GC_TEST_DUMP");
    if (gc_test_dump_env && strcmp(gc_test_dump_env, "1") == 0) {
        gc.test_dump = 1;
    }

    char *gc_test_dump_color_env = getenv("GC_TEST_DUMP_COLOR");
    if (gc_test_dump_color_env && strcmp(gc_test_dump_color_env, "1") == 0) {
        gc.test_dump_color = 1;
    }

    gc_log(1, "Initialize GC with log level: %i\n", gc.log_level);

#include <sys/mman.h>
#include <errno.h>

    gc.pool = mmap((void *)POOL_START, POOL_SIZE, PROT_READ|PROT_WRITE, MAP_PRIVATE|MAP_FIXED|MAP_ANONYMOUS, -1, 0);
    gc_log(2, "Allocate test GC memory pool: mmap returned %p (%s)\n", gc.pool, strerror(errno));
    assert(errno == 0);

    gc_log(3, "memset %#02x at %p for %i bytes\n", FREE, gc.pool, POOL_SIZE);
    memset(gc.pool, FREE, POOL_SIZE);
    memset(gc.pool, BOUNDARY, 2 * sizeof(int64_t));
    memset(gc.pool + POOL_SIZE - 2 * sizeof(int64_t), BOUNDARY, 2 * sizeof(int64_t));

    gc.pool_free = gc.pool + 2 * sizeof(int64_t);
#endif // #ifdef GC_TEST
}

void gc_run() {
    if (!gc.enable) {
        return;
    }

    gc_log(2, "Start GC\n");

    GcBlock *block = gc.blocks_chain;
    while (block) {
        block->state = Unreachable;
        gc_block_print(block);
        block = block->next;
    }

    LlvmStackFrame *frame = llvm_gc_root_chain;
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

    GcBlock *prev = NULL;
    block = gc.blocks_chain;
    while (block) {
        gc_block_print(block);
        if (block->state == Unreachable) {
            if (block == gc.blocks_chain) {
                gc.blocks_chain = block->next;
            } else {
                assert(prev != NULL);
                prev->next = block->next;
            }
            GcBlock *next = block->next;
            gc_log(1, "freeing block at %p (object size: %li)\n", block, block->data_size);
            gc_free(block);
            block = next;
        } else {
            prev = block;
            block = block->next;
        }
    }
}

void gc_mark_visitor(int depth, void *object, const Meta *meta) {
    GcBlock *block = object - sizeof(GcBlock);

    gc_ident(2, depth);
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

    gc_ident(3, depth);
    gc_log(3, "      (cnt) meta[0]=%li\n", meta[0]);
    for (int64_t i = 0; i < meta[0]; i++) {
        gc_ident(3, depth);
        gc_log(3, "      (off) meta[%li]=%li\n", 1 + i*2, meta[1 + i*2]);
        gc_ident(3, depth);
        gc_log(3, "      (met) meta[%li]=%p\n", 1 + i*2 + 1, (void *)meta[1 + i*2 + 1]);

        int64_t offset = meta[1 + i*2];
        void *child_offset = object + offset;
        void *child = (void *)*(int64_t *)child_offset;

        gc_ident(2, depth);
        gc_log(2, "        %li. %p(+%li) -> %p\n", i, child_offset, offset, child);

        const Meta *child_meta = (Meta *)(void *)meta[1 + i*2 + 1];

        gc_mark_visitor(depth + 1, child, child_meta);
    }
}

void* gc_malloc(int64_t data_size) {
    gc_run();

    size_t alloc_size = sizeof(GcBlock) + data_size;

#ifdef GC_TEST
    GcBlock *block = (void *)gc.pool_free;
    gc.pool_free += alloc_size;
    gc_log(3, "memset %#02x at %p for %li bytes\n", ALLOCATED, block, alloc_size);
    memset(block, ALLOCATED, alloc_size);
#else
    GcBlock *block = malloc(alloc_size);
#endif // #ifdef GC_TEST

    block->state = Unreachable;
    block->data_size = data_size;
    block->next = gc.blocks_chain;
    gc.blocks_chain = block;

    gc_log(1, "allocated block of size %li at %p, returning object of size %li at %p(+%li)\n",
        alloc_size,
        block,
        data_size,
        &block->data,
        (uint8_t *)block->data - (uint8_t *)block
    );

    return &block->data;
}

void gc_free(GcBlock *block) {
#ifdef GC_TEST
    gc_log(3, "memset %#02x at %p for %li bytes\n", FREED, block, sizeof(GcBlock) + block->data_size);

    if (gc.test_dump_color) {
        // todo mutually exclusive: memset and coloring
        block->next = gc.freed_blocks_chain;
        gc.freed_blocks_chain = block;
    } else {
        memset((void *)block, FREED, sizeof(GcBlock) + block->data_size);
    }

#else
    free(block);
#endif // #ifdef GC_TEST
}


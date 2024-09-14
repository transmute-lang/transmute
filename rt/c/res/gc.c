// defines:
//  - GC_TEST: compile with test mode support
//
// standard env. variables
//  - GC_ENABLE: if set to 0, GC is not executed
//
// test mode env. variables
//  - GC_TEST_POOL_SIZE:  if set, the pool size; otherwise it takes the value of the DEFAULT_POOL_SIZE constant
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

// todo trigger actual GC only if some conditions hold
// todo keep track of freed blocks to return them instead of a full cycle of free/malloc syscalls

#ifdef GC_TEST
#define BOUNDARY             0xBB
#define FREE                 0xFF
#define ALLOCATED            0xAA
#define FREED                0xDD
#define POOL_START           65536

#ifndef BOUNDARY_SIZE
#define BOUNDARY_SIZE        16
#endif // #ifndef BOUNDARY_SIZE

#ifndef DEFAULT_POOL_SIZE
#define DEFAULT_POOL_SIZE    512
#endif // #ifndef DEFAULT_POOL_SIZE
#endif // #ifdef GC_TEST

typedef struct GcStructField {
    size_t                 offset;
    struct GcStructLayout *layout;
} GcStructField;

typedef struct GcStructLayout {
    size_t                 count;
    GcStructField          fields[0];
} GcStructLayout;

typedef enum GcBlockState {
    Unreachable = 0,
    Reachable   = 1
} GcBlockState;

static inline char* state_to_char(GcBlockState state) {
    switch (state) {
        case Unreachable: return "unreachable";
        case Reachable: return "reachable";
        default: {
            fprintf(stderr, "PANIC: Invalid state: %i\n", (int)state);
            exit(1);
        };
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

    int execution_count;

    int alloc_count;
    size_t total_alloc_sz;
    size_t object_alloc_sz;

    int free_count;
    size_t total_free_sz;
    size_t object_free_sz;

    size_t current_alloc_sz;
    size_t current_object_alloc_sz;

    size_t max_alloc_sz;
    size_t max_object_alloc_sz;

    #ifdef GC_TEST
    GcBlock *freed_blocks_chain;
    size_t pool_size;
    uint8_t *pool;
    uint8_t *pool_free;
    int log_level;
    int test_dump;
    int test_dump_color;
    #endif // #ifdef GC_TEST
} Gc;

Gc gc = {
    .enable = 1,
    .blocks_chain = NULL,

    .execution_count = 0,

    .alloc_count = 0,
    .total_alloc_sz = 0,
    .object_alloc_sz = 0,

    .free_count = 0,
    .total_free_sz = 0,
    .object_free_sz = 0,

    .current_alloc_sz = 0,
    .current_object_alloc_sz = 0,

    .max_alloc_sz = 0,
    .max_object_alloc_sz = 0,

    #ifdef GC_TEST
    .freed_blocks_chain = NULL,
    .pool_size = DEFAULT_POOL_SIZE,
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
void gc_mark_visitor(int depth, void *object, const GcStructLayout *layout);


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

    printf("\nMemory dump:\n\n");
    for (size_t i = 0; i < gc.pool_size + 2*BOUNDARY_SIZE; i++) {
        if (i == 0) {
            printf("    %p    ", &gc.pool[i]);
        } else if (i % 16 == 0) {
           printf("\n    %p    ", &gc.pool[i]);
        } else if (i % 4 == 0) {
            printf("  ");
        }

        if (gc.test_dump_color) {
            if (i < BOUNDARY_SIZE || i >= gc.pool_size + BOUNDARY_SIZE) {
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

void gc_print_statistics() {
    printf("\nStatistics:\n\n");
    printf("  Executions            %4i\n", gc.execution_count);
    printf("  Alloc                 %4i blocks\n", gc.alloc_count);
    printf("  Free                  %4i blocks\n", gc.free_count);
    printf("  Total alloc           %4li bytes\n", gc.total_alloc_sz);
    printf("  Object alloc          %4li bytes\n", gc.object_alloc_sz);
    printf("  Total free            %4li bytes\n", gc.total_free_sz);
    printf("  Object free           %4li bytes\n", gc.object_free_sz);
    printf("  Max alloc             %4li bytes\n", gc.max_alloc_sz);
    printf("  Max object alloc      %4li bytes\n", gc.max_object_alloc_sz);
    printf("  Current alloc         %4li bytes\n", gc.current_alloc_sz);
    printf("  Current object alloc  %4li bytes\n", gc.current_object_alloc_sz);
    printf("\n");
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

    char *gc_test_pool_size = getenv("GC_TEST_POOL_SIZE");
    if (gc_test_pool_size) {
        gc.pool_size = atoi(gc_test_pool_size);
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

    gc.pool = mmap(
        (void *)POOL_START,
        gc.pool_size + 2 * BOUNDARY_SIZE,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS,
        -1,
        0
    );
    gc_log(2, "Allocate test GC memory pool (%li bytes): mmap returned %p (%s)\n",
        gc.pool_size + 2 * BOUNDARY_SIZE,
        gc.pool,
        strerror(errno)
    );
    assert(errno == 0);

    gc_log(3, "memset %#02x at %p for %i bytes\n", FREE, gc.pool, gc.pool_size);
    memset(gc.pool, BOUNDARY, BOUNDARY_SIZE);
    memset(gc.pool + BOUNDARY_SIZE, FREE, gc.pool_size);
    memset(gc.pool + gc.pool_size + BOUNDARY_SIZE, BOUNDARY, BOUNDARY_SIZE);

    gc.pool_free = gc.pool + BOUNDARY_SIZE;

    gc_pool_dump();
#endif // #ifdef GC_TEST
}

void gc_run() {
    if (!gc.enable) {
        return;
    }

    gc.execution_count++;

    gc_log(2, "Start GC\n");

    GcBlock *block = gc.blocks_chain;
    while (block) {
        block->state = Unreachable;
        gc_block_print(block);
        block = block->next;
    }

    LlvmStackFrame *frame = llvm_gc_root_chain;
    for (int frame_idx = 0; frame; frame_idx++) {
        // all roots have a meta associated
        assert(frame->map->num_roots == frame->map->num_meta);

        gc_log(2, "  frame %i (%i roots)", frame_idx, frame->map->num_roots);
        gc_log(3, " at %p", frame);
        gc_log(2, ":\n");

        for (int32_t root_idx = 0; root_idx < frame->map->num_roots; root_idx++) {
            if (frame->roots[root_idx]) {
                gc_log(2, "    root %i:\n", root_idx);
                gc_mark_visitor(0, frame->roots[root_idx], frame->map->meta[root_idx]);
            } else {
                gc_log(2, "    root %i: skipped (nil)\n", root_idx);
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

void gc_mark_visitor(int depth, void *object, const GcStructLayout *layout) {
    GcBlock *block = object - sizeof(GcBlock);

#ifdef GC_TEST
    gc_ident(2, depth);
    if (gc.log_level >= 3) {
        gc_log(3, "      object at %p (block at %p): %li pointers (layout %p), %s\n",
            object,
            block,
            layout->count,
            layout,
            state_to_char(block->state)
        );
    } else {
        gc_log(2, "      object at %p (block at %p): %li pointers, %s\n",
            object,
            block,
            layout->count,
            state_to_char(block->state)
        );
    }
#endif // #ifdef GC_TEST

    if (block->state == Reachable) {
        return;
    }
    block->state = Reachable;

    gc_ident(3, depth);
    gc_log(3, "         layout->count=%li\n", layout->count);
    for (int64_t i = 0; i < layout->count; i++) {
        gc_ident(3, depth);
        gc_log(3, "         layout->fields[%li].offset=%li\n", i, layout->fields[i].offset);
        gc_ident(3, depth);
        gc_log(3, "         layout->fields[%li].layout=%p\n", i, (void *)layout->fields[i].layout);

        int64_t offset = layout->fields[i].offset;
        void *child_offset = object + offset;
        void *child = (void *)*(int64_t *)child_offset;

        gc_ident(2, depth);
        gc_log(2, "        %li. %p(+%li) -> %p\n", i, child_offset, offset, child);

        const GcStructLayout *child_layout = layout->fields[i].layout;

        gc_mark_visitor(depth + 1, child, child_layout);
    }
}

void* gc_malloc(int64_t data_size) {
    gc_run();

    size_t alloc_size = sizeof(GcBlock) + data_size;

#ifdef GC_TEST
    if (gc.pool_free + alloc_size >= gc.pool + gc.pool_size + BOUNDARY_SIZE) {
        fprintf(stderr, "\nERROR: Cannot allocate %li bytes: missing %li bytes\n",
            alloc_size,
            gc.pool_free + alloc_size - (gc.pool + gc.pool_size + BOUNDARY_SIZE)
        );
        gc_pool_dump();
        gc_print_statistics();
        exit(1);
    }

    GcBlock *block = (void *)gc.pool_free;
    gc.pool_free += alloc_size;
    gc_log(3, "memset %#02x at %p for %li bytes\n", ALLOCATED, block, alloc_size);
    memset(block, ALLOCATED, alloc_size);
#else
    GcBlock *block = malloc(alloc_size);
#endif // #ifdef GC_TEST

    gc.alloc_count++;
    gc.total_alloc_sz += alloc_size;
    gc.current_alloc_sz += alloc_size;
    gc.object_alloc_sz += data_size;
    gc.current_object_alloc_sz += data_size;
    if (gc.current_alloc_sz > gc.max_alloc_sz) {
        gc.max_alloc_sz = gc.current_alloc_sz;
    }
    if (gc.current_object_alloc_sz > gc.max_object_alloc_sz) {
        gc.max_object_alloc_sz = gc.current_object_alloc_sz;
    }

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

    gc.free_count++;
    gc.total_free_sz += sizeof(GcBlock) + block->data_size;
    gc.current_alloc_sz -= sizeof(GcBlock) + block->data_size;
    gc.object_free_sz += block->data_size;
    gc.current_object_alloc_sz -= block->data_size;

    if (gc.test_dump_color) {
        block->next = gc.freed_blocks_chain;
        gc.freed_blocks_chain = block;
    } else {
        memset((void *)block, FREED, sizeof(GcBlock) + block->data_size);
    }

#else
    free(block);
#endif // #ifdef GC_TEST
}

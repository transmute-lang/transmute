// defines:
//  - GC_TEST:            compile with test mode support
//  - GC_LOGS:            compile with logs support
//
// standard env. variables
//  - GC_ENABLE:          if set to 0, GC is not executed
//  - GC_PRINT_STATS:     if set to 1, GC stats are printed at the end of execution
//
// if compiled with GC_LOGS:
//  - GC_LOG_LEVEL:       if set to 1, print GC messages; if set to 2, print more GC messages, etc.
//
// if compiled with GC_TEST:
//  - GC_TEST_POOL_SIZE:  if set, the pool size; otherwise it takes the value of the DEFAULT_POOL_SIZE constant
//  - GC_TEST_DUMP:       if set to 1, a memory dump is printed to stdout at the end of program execution
//  - GC_TEST_DUMP_COLOR: if set to 1, the memory dump is colored (implied GC_TEST_DUMP=1)
//  - GC_TEST_FINAL_RUN:  if set to 0, the GC is not run during the teardown phase
//  - GC_PRINT_STATS:     has no effect, stats are displayed anyway at the end of execution

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#include "llvm.h"
#include "gc.h"
#include "bindings/rust.h"

extern LlvmStackFrame *llvm_gc_root_chain;

// todo:feature trigger actual GC only if some conditions hold
// todo:feature keep track of freed blocks to return them instead of a full cycle of free/malloc syscalls

#define PANIC(msg)                                                       \
do {                                                                     \
    fprintf(stderr, "\nGC PANIC: "msg" (%s:%i)\n", __FILE__, __LINE__);  \
    exit(1);                                                             \
} while (0)

#define PANIC_ARGS(msg, ...)                                                          \
do {                                                                                  \
    fprintf(stderr, "\nGC PANIC: "msg" (%s:%i)\n", __VA_ARGS__, __FILE__, __LINE__);  \
    exit(1);                                                                          \
} while (0)

#ifdef GC_TEST
#include <sys/mman.h>
#include <errno.h>

#ifndef GC_LOGS
#define GC_LOGS
#endif // ifndef GC_LOGS

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
#endif // GC_TEST

#ifdef GC_LOGS
#define LOG(level, depth, ...) \
    gc_log(level, depth, __func__, __LINE__, __VA_ARGS__)
#define LOG_BLOCK(block) \
    gc_block_print(block)
#else
#define LOG(level, depth, ...)
#define LOG_BLOCK(block)
#endif

#define GC_BLOCK(object) ((GcBlock *)((char *)object - sizeof(GcBlock)))

typedef enum GcBlockState {
    Unreachable = 0,
    Reachable   = 1,
    Owned       = 2,
} GcBlockState;

static inline char* state_to_char(GcBlockState state) {
    switch (state) {
        case Unreachable: return "unreachable";
        case Reachable: return "reachable";
        case Owned: return "owned";
        default: {
            PANIC_ARGS("Invalid state: %i", (int)state);
        };
    }
}

static inline char* gc_pointee_kind_tag_to_char(GcPointeeKindTag tag) {
    switch (tag) {
        case Struct: return "struct";
        case Array: return "array";
        case Managed: return "managed";
        default: {
            PANIC_ARGS("Invalid pointee kind: %i", (int)tag);
        };
    }
}

typedef struct GcBlock {        // 24 bytes
    GcBlockState     state;     //  8 (4 + 4)
    struct GcBlock  *next;      //  8
    size_t           data_size; //  8
    uint8_t          data[];    //  0
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

#ifdef GC_LOGS
    int log_level;
#endif // GC_LOGS

#ifdef GC_TEST
    GcBlock *freed_blocks_chain;
    size_t pool_size;
    uint8_t *pool;
    uint8_t *pool_free;
    int test_final_run;
    int test_dump;
    int test_dump_color;
#endif // GC_TEST
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

#ifdef GC_LOGS
    .log_level = 0,
#endif // GC_LOGS

#ifdef GC_TEST
    .freed_blocks_chain = NULL,
    .pool_size = DEFAULT_POOL_SIZE,
    .pool = NULL,
    .pool_free = NULL,
    .test_final_run = 1,
    .test_dump = 0,
    .test_dump_color = 0,
#endif // GC_TEST
};

void gc_free(GcBlock *block);
void gc_mark(int depth, void *object, const GcPointeeLayout *layout);

#ifdef GC_LOGS
static inline void gc_log(int level, int depth, const char* func, int line, const char *fmt, ...) {
    if (gc.log_level >= level) {
        for (int i = 0; i < depth; i++) {
            printf("  ");
        }
        printf("[%i] %-22s %i | ", level, func, line);
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
}

void gc_block_print(GcBlock *block) {
    gc_log(2, 0, "gc_block_print", __LINE__, "  block at %p (object at %p): %s\n",
        block,
        (char *)block + sizeof(GcBlock),
        state_to_char(block->state)
    );
}
#endif // GC_LOGS

#ifdef GC_TEST
#define COLOR_WHITE 0
#define COLOR_GREEN 32
#define COLOR_RED   31
#define COLOR_BLUE  34

static inline void print_byte(uint8_t byte, bool print_char, int color) {
    if (print_char) {
        if (byte > 31 && byte < 127) {
            printf("\033[%im%c\033[0m", color, byte);
        }
        else {
            printf("\033[%im.\033[0m", color);
        }
    }
    else {
        printf("\033[%im%02x\033[0m ", color, byte);
    }
}

void gc_pool_dump() {
    printf("\nMemory dump:\n\n");
    bool print_chars = false;
    for (size_t i = 0; /* nothing */; i++) {
        if (print_chars && i == gc.pool_size + 2 * BOUNDARY_SIZE) {
            break;
        }
        if (i == 0) {
            if (!print_chars) {
                printf("    %p    ", (void *)&gc.pool[i]);
            }
        }
        else if (i % 16 == 0) {
            if (print_chars) {
                print_chars = false;
                printf("\n    %p    ", (void *)&gc.pool[i]);
            }
            else {
                printf("   ");
                print_chars = true;
                i -= 16;
            }
        }
        else if (i % 4 == 0) {
            printf("  ");
        }

        if (gc.test_dump_color) {
            if (i < BOUNDARY_SIZE || i >= gc.pool_size + BOUNDARY_SIZE) {
                print_byte(gc.pool[i], print_chars, COLOR_RED);
            }
            else if (i >= gc.pool_free - gc.pool) {
                print_byte(gc.pool[i], print_chars, COLOR_BLUE);
            }
            else {
                int freed = 0;
                char *byte_addr = (char *)&gc.pool[i];
                GcBlock *block = gc.freed_blocks_chain;
                while (block) {
                    if (byte_addr >= (char *)block && byte_addr < (char *)(block + 1) + block->data_size) {
                        print_byte(gc.pool[i], print_chars, COLOR_GREEN);
                        freed = 1;
                        break;
                    }
                    block = block->next;
                }
                if (!freed) {
                    print_byte(gc.pool[i], print_chars, COLOR_WHITE);
                }
            }
        }
        else {
            print_byte(gc.pool[i], print_chars, COLOR_WHITE);
        }
    }
    printf("\n\n");
}
#endif // GC_TEST

void gc_print_statistics() {
    printf("\nStatistics:\n\n");
    printf("  Executions ......%4i\n", gc.execution_count);
    printf("  Allocated .......%4i blocks\n", gc.alloc_count);
    printf("    Total\n");
    printf("      objects      %4li bytes\n", gc.object_alloc_sz);
    printf("      blocks       %4li bytes\n", gc.total_alloc_sz);
    printf("    Max\n");
    printf("      objects      %4li bytes\n", gc.max_object_alloc_sz);
    printf("      blocks       %4li bytes\n", gc.max_alloc_sz);
    printf("    End\n");
    printf("      objects      %4li bytes\n", gc.current_object_alloc_sz);
    printf("      blocks       %4li bytes\n", gc.current_alloc_sz);
    printf("  Freed ...........%4i blocks\n", gc.free_count);
    printf("    Total\n");
    printf("      objects      %4li bytes\n", gc.object_free_sz);
    printf("      blocks       %4li bytes\n", gc.total_free_sz);
    printf("\n");
}

void gc_init() {
    char *gc_enable_env = getenv("GC_ENABLE");
    if (gc_enable_env && strcmp(gc_enable_env, "0") == 0) {
        gc.enable = 0;
    }

#ifdef GC_LOGS
    char *gc_test_log_env = getenv("GC_LOG_LEVEL");
    if (gc_test_log_env) {
        gc.log_level = atoi(gc_test_log_env);
    }
#endif // GC_LOGS

LOG(1, 0, "Initialize GC with log level: %i\n", gc.log_level);

#ifdef GC_TEST
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

    char *gc_test_final_run = getenv("GC_TEST_FINAL_RUN");
    if (gc_test_final_run && strcmp(gc_test_final_run, "0") == 0) {
        gc.test_final_run = 0;
    }

    gc.pool = mmap(
        (void *)POOL_START,
        gc.pool_size + 2 * BOUNDARY_SIZE,
        PROT_READ | PROT_WRITE,
        MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS,
        -1,
        0
    );
    LOG(2, 0, "Allocate test GC memory pool (%li bytes): mmap returned %p (%s)\n",
        gc.pool_size + 2 * BOUNDARY_SIZE,
        gc.pool,
        strerror(errno)
    );
    assert(errno == 0);

    LOG(3, 0, "memset %#02x at %p for %i bytes\n", FREE, gc.pool, gc.pool_size);
    memset(gc.pool, BOUNDARY, BOUNDARY_SIZE);
    memset(gc.pool + BOUNDARY_SIZE, FREE, gc.pool_size);
    memset(gc.pool + gc.pool_size + BOUNDARY_SIZE, BOUNDARY, BOUNDARY_SIZE);

    gc.pool_free = gc.pool + BOUNDARY_SIZE;

    if (gc.test_dump) {
        gc_pool_dump();
    }
#endif // GC_TEST
}

void gc_teardown() {
    LOG(2, 0, "GC Teardown\n");

#ifdef GC_TEST
    if (gc.test_final_run) {
        // no blocks are reachable anymore
        llvm_gc_root_chain = NULL;
        gc_run(); // we don't run the gc in non test mode as the OS will free all remaining memory for us anyway
    }

    if (gc.test_dump) {
        gc_pool_dump();
    }
    gc_print_statistics();
    assert(munmap((void *)gc.pool, gc.pool_size + 2 * BOUNDARY_SIZE) == 0);
#else
    char *gc_print_stats_env = getenv("GC_PRINT_STATS");
    if (gc_print_stats_env && strcmp(gc_print_stats_env, "1") == 0) {
        gc_print_statistics();
    }
#endif // GC_TEST
}

void gc_run() {
    if (!gc.enable) {
        return;
    }

    gc.execution_count++;

    LOG(2, 0, "Start GC\n");
    if (gc.blocks_chain == NULL) {
        LOG(2, 0, "no allocated blocks\n");
        return;
    }

    LOG(2, 0, "Phase: init.\n");
    GcBlock *block = gc.blocks_chain;
    while (block) {
        if (block->state != Owned) {
            block->state = Unreachable;
        }
        LOG_BLOCK(block);
        block = block->next;
    }

    LOG(2, 0, "Phase: mark\n");
    LlvmStackFrame *frame = llvm_gc_root_chain;
    for (int frame_idx = 0; frame; frame_idx++) {
        // all roots have a meta associated
        assert(frame->map->num_roots == frame->map->num_meta);

        LOG(2, 0, "  frame %i (%i roots) at frame %p:\n", frame_idx, frame->map->num_roots, frame);

        for (int32_t root_idx = 0; root_idx < frame->map->num_roots; root_idx++) {
            if (frame->roots[root_idx]) {
                LOG(2, 0, "    root %i:\n", root_idx);
                gc_mark(0, frame->roots[root_idx], frame->map->meta[root_idx]);
            }
            else {
                LOG(2, 0, "    root %i: skipped (null)\n", root_idx);
            }
        }

        frame = frame->next;
    }

    LOG(2, 0, "Phase: sweep\n");
    GcBlock *prev = NULL;
    block = gc.blocks_chain;
    while (block) {
        LOG_BLOCK(block);
        if (block->state == Unreachable) {
            if (block == gc.blocks_chain) {
                gc.blocks_chain = block->next;
            }
            else {
                assert(prev != NULL);
                prev->next = block->next;
            }
            GcBlock *next = block->next;
            LOG(1, 0, "freeing block at %p (object size: %li)\n", block, block->data_size);
            gc_free(block);
            block = next;
        }
        else {
            LOG(1, 0, "keeping block at %p (object size: %li): %s\n",
                block, block->data_size, state_to_char(block->state));
            prev = block;
            block = block->next;
        }
    }
}

void gc_mark(int depth, void *object, const GcPointeeLayout *layout) {
    GcBlock *block = GC_BLOCK(object);

#ifdef GC_LOGS
    if (gc.log_level >= 3) {
        LOG(3, depth, "      %s %s block at %p (object at %p): %li pointers (layout %p)\n",
            state_to_char(block->state),
            gc_pointee_kind_tag_to_char(layout->tag),
            block,
            object,
            layout->count,
            layout
        );
    }
    else {
        LOG(2, depth, "      %s %s block at %p (object at %p): %li pointers\n",
            state_to_char(block->state),
            gc_pointee_kind_tag_to_char(layout->tag),
            block,
            object,
            layout->count
        );
    }
#endif // GC_LOGS

    if (block->state == Reachable) {
        return;
    }
    block->state = Reachable;

    switch (layout->tag) {
        case Struct: {
            LOG(3, depth, "      -fields count: %li\n", layout->count);
            for (size_t i = 0; i < layout->count; i++) {
                GcStructField field = layout->pointee.struct_fields[i];
                int64_t offset = field.offset;
                const GcPointeeLayout *child_layout = field.layout;

                LOG(3, depth, "      -fields[%li] offset: %li\n", i, offset);
                LOG(3, depth, "      -fields[%li] layout: %p\n", i, (void *)child_layout);

                void *child_offset = (char *)object + offset;
                void *child = (void *)*(size_t *)child_offset;
                LOG(2, depth, "        %li. %p(+%li) -> %p\n", i, child_offset, offset, child);

                gc_mark(depth + 1, child, child_layout);
            }
            break;
        }
        case Array: {
            GcPointeeLayout *child_layout = layout->pointee.array_element.layout;

            LOG(3, depth, "      -elements count: %li\n", layout->count);
            LOG(3, depth, "      -elements layout: %p\n", (void *)child_layout);

            if (child_layout) {
                void **array = (void **)object;
                for (size_t i = 0; i < layout->count; i++) {
                    LOG(2, depth, "        %li. %p(+%li) -> %p\n", i, &array[i], i * sizeof(void *), array[i]);
                }
            }
            break;
        }
        case Managed: {
            LOG(2, depth, "        %p: mark(%p) @ %p\n", (void *)block, block->data, (*(Metadata*)block->data).mark);
            (*(Metadata*)block->data).mark(block->data);
        }
    }
}

void* gc_malloc(size_t data_size, size_t align) {
    LOG(2, 0, "alloc %li bytes, align: %li (header: %li bytes)\n", data_size, align);
    gc_run();

    size_t alloc_size = sizeof(GcBlock) + data_size;

#ifdef GC_TEST
    // assert(sizeof(GcBlock) % align == 0);
    // fixme this works for as long as the header is a multiple of align
    // fixme we need to implement the same feature for malloc, when the header is not a multiple of align
    gc.pool_free = (uint8_t *)(((uintptr_t)gc.pool_free + (align - 1)) & -align);

    if (gc.pool_free + alloc_size >= gc.pool + gc.pool_size + BOUNDARY_SIZE) {
        if (gc.test_dump) {
            gc_pool_dump();
        }
        gc_print_statistics();
        PANIC_ARGS("Cannot allocate %li bytes: missing %li bytes",
            alloc_size,
            gc.pool_free + alloc_size - (gc.pool + gc.pool_size + BOUNDARY_SIZE)
        );
    }

    GcBlock *block = (void *)gc.pool_free;
    gc.pool_free += alloc_size;
    LOG(3, 0, "memset %#02x at %p for %li bytes\n", ALLOCATED, block, alloc_size);
    memset(block, ALLOCATED, alloc_size);
#else
    GcBlock *block = malloc(alloc_size);
    assert(block != NULL);
#endif // GC_TEST

    block->state = Unreachable;
    block->data_size = data_size;
    block->next = gc.blocks_chain;
    gc.blocks_chain = block;

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

    LOG(1, 0, "allocated block of size %li at %p, returning object of size %li at %p(+%li)\n",
        alloc_size,
        block,
        data_size,
        &block->data,
        (uint8_t *)block->data - (uint8_t *)block
    );

    return &block->data;
}

void gc_free(GcBlock *block) {
    gc.free_count++;
    gc.total_free_sz += sizeof(GcBlock) + block->data_size;
    gc.current_alloc_sz -= sizeof(GcBlock) + block->data_size;
    gc.object_free_sz += block->data_size;
    gc.current_object_alloc_sz -= block->data_size;

#ifdef GC_TEST
    if (gc.test_dump_color) {
        block->next = gc.freed_blocks_chain;
        gc.freed_blocks_chain = block;
    }
    else {
        LOG(3, 0, "memset %#02x at %p for %li bytes\n", FREED, block, sizeof(GcBlock) + block->data_size);
        memset((void *)block, FREED, sizeof(GcBlock) + block->data_size);
    }
#else
    free(block);
#endif // GC_TEST
}

void gc_take_ownership(void *object) {
    GcBlock *block = GC_BLOCK(object);
    LOG(2, 0, "mark block at %p (object at %p) as owned\n", block, object);
    block->state = Owned;
}

void gc_release_ownership(void *object) {
    GcBlock *block = GC_BLOCK(object);
    LOG(2, 0, "mark owned block at %p (object at %p) as unreachable\n", block, object);
    block->state = Unreachable;
}

void gc_mark_managed(void * object) {
    GcBlock *block = GC_BLOCK(object);
//    LOG(2, 0, "mark managed block at %p (object at %p) as reachable\n", block, object);
    block->state = Reachable;
}

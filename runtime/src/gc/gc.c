// defines:
//  - GC_TEST:            compile with test mode support
//  - GC_LOGS:            compile with logs support
//  - GC_LOGS_STABLE:     compile with stable logs support
//  - GC_LOGS_COLOR:      compile with colored logs support
//  - GC_PTHREAD          compile with multi-threading support using pthread
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

#include <assert.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "../llvm/llvm.h"
#include "gc.h"

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

#define TODO(msg)                                                     \
 do {                                                                 \
     fprintf(stderr, "\nTODO: "msg" (%s:%i)\n", __FILE__, __LINE__);  \
     exit(1);                                                         \
 } while (0)

#define COLOR_WHITE 0
#define COLOR_GREEN 32
#define COLOR_RED   31
#define COLOR_BLUE  34

#ifdef GC_LOGS_COLOR
    #define COLOR_START_WHITE "\033[0m"
    #define COLOR_START_GREEN "\033[32m"
    #define COLOR_START_RED "\033[31m"
    #define COLOR_START_BLUE "\033[34m"
    #define COLOR_END "\033[0m"
#else // GC_LOGS_COLOR
    #define COLOR_START_WHITE ""
    #define COLOR_START_GREEN ""
    #define COLOR_START_RED ""
    #define COLOR_START_BLUE ""
    #define COLOR_END ""
#endif // GC_LOGS_COLOR

#ifdef GC_TEST
#include <sys/mman.h>
#include <errno.h>

// if in GC_TEST we define GC_LOGS
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
#define LOG(level, ...) \
    gc_log(level, __func__, __LINE__, __VA_ARGS__)
#else
#define LOG(level, ...)
#endif

#ifdef __APPLE__
// we pretend that we mmap'ed at the correct location...
#define POOL_OFFSET(ptr)     ((void*)((uintptr_t)ptr - (uintptr_t)gc.pool + POOL_START))
#else
#define POOL_OFFSET(ptr)     ((void*)ptr)
#endif // __APPLE__

typedef enum GcBlockState {
    Unreachable = 0,
    Reachable   = 1,
    Owned       = 2,
} GcBlockState;

#if defined(GC_LOGS) || defined(GC_TEST)
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
#endif // defined(GC_LOGS) || defined(GC_TEST)

typedef struct GcBlock {         // 32 or 48 bytes
    GcBlockState     state;      //  8 (4 + 4)
    struct GcBlock  *next;       //  8
    size_t           data_size;  //  8
    GcCallbacks     *callbacks;  //  8
#ifdef GC_TEST
    char            *name;       //  8
#endif // GC_TEST
} GcBlock;

#define GC_BLOCK_DIVISIBILITY 16
// rounds sizeof(GcBlock) to the nearest upper (including itself) multiple of GC_BLOCK_DIVISIBILITY
#define GC_BLOCK_SIZE         ((sizeof(GcBlock) + (GC_BLOCK_DIVISIBILITY - 1)) & (~(GC_BLOCK_DIVISIBILITY - 1)))
#define GC_BLOCK(object)      ((GcBlock *)((uintptr_t)object - GC_BLOCK_SIZE))
#define GC_OBJECT(block)      ((void *)((uintptr_t)block + GC_BLOCK_SIZE))

typedef struct Gc {
#ifdef GC_PTHREAD
    pthread_mutex_t lock;
#endif // GC_PTHREAD
    bool initialized;
    bool enable;
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

#ifdef GC_PTHREAD
static pthread_mutex_t gc_init_mutex = PTHREAD_MUTEX_INITIALIZER;
#endif // GC_PTHREAD

Gc gc = {
#ifdef GC_PTHREAD
    .lock = { 0 },
#endif // GC_PTHREAD
    .initialized = false,
    .enable = true,
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

#ifdef GC_LOGS
static inline void gc_log(int level, const char* func, int line, const char *fmt, ...) {
    if (gc.log_level >= level) {
#ifdef GC_LOGS_STABLE
        printf("[%i] %-22s | ", level, func);
#else
        printf("[%i] %-22s %i | ", level, func, line);
#endif // GC_LOGS_STABLE
        va_list args;
        va_start(args, fmt);
        vprintf(fmt, args);
        va_end(args);
    }
}
#endif // GC_LOGS

#ifdef GC_TEST
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

static inline bool inside_block(uintptr_t addr, GcBlock *block) {
    bool after_block_begin = addr >= (uintptr_t)block;
    bool before_block_end = addr < (uintptr_t)block + GC_BLOCK_SIZE + block->data_size;
    return after_block_begin && before_block_end;
}

void gc_pool_dump(void) {
    printf("\nMemory dump:\n\n");

    printf("  \033[%imboundary\033[0m \033[%imused\033[0m \033[%imfreed\033[0m \033[%imleft\033[0m\n\n",
      COLOR_RED, COLOR_WHITE, COLOR_GREEN, COLOR_BLUE);

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
                uintptr_t byte_addr = (uintptr_t)&gc.pool[i];
                GcBlock *block = gc.freed_blocks_chain;
                while (block) {
                    if (inside_block(byte_addr, block)) {
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

    printf("\n\n  \033[%imboundary\033[0m \033[%imused\033[0m \033[%imfreed\033[0m \033[%imleft\033[0m\n\n",
          COLOR_RED, COLOR_WHITE, COLOR_GREEN, COLOR_BLUE);
}

void gc_set_object_name(void *object, char *name) {
    GC_BLOCK(object)->name = name;
}
#endif // GC_TEST

void gc_print_statistics(void) {
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

void gc_init(void) {
    if (gc.initialized) {
        LOG(3, "already initialized\n");
        return;
    }
    assert(GC_BLOCK_SIZE % 16 == 0);

#ifdef GC_PTHREAD
    if (pthread_mutex_trylock(&gc_init_mutex) != 0) {
        LOG(3, "being initialized\n");
        return;
    }

    pthread_mutexattr_t mutex_attr;
    if (pthread_mutexattr_init(&mutex_attr) != 0) {
        PANIC("Could not initialize mutex attributes");
    }
    if (pthread_mutexattr_settype(&mutex_attr, PTHREAD_MUTEX_RECURSIVE) != 0) {
        PANIC("Could not initialize mutex kind");
    }
    if (pthread_mutex_init(&gc.lock, &mutex_attr) != 0) {
        PANIC("Could not initialize mutex");
    }
    if (pthread_mutexattr_destroy(&mutex_attr) != 0) {
#ifdef GC_TEST
        PANIC("Could not destroy mutex attributes");
#endif // GC_TEST
    }
#endif // GC_PTHREAD

    char *gc_enable_env = getenv("GC_ENABLE");
    if (gc_enable_env && strcmp(gc_enable_env, "0") == 0) {
        gc.enable = false;
    }

#ifdef GC_LOGS
    char *gc_test_log_env = getenv("GC_LOG_LEVEL");
    if (gc_test_log_env) {
        gc.log_level = atoi(gc_test_log_env);
    }
#endif // GC_LOGS

LOG(1,  "Initialize GC with log level: %i\n", gc.log_level);

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
#ifdef __APPLE__
        MAP_PRIVATE | MAP_ANONYMOUS,
#else
        MAP_PRIVATE | MAP_FIXED | MAP_ANONYMOUS,
#endif // errno
        -1,
        0
    );

#ifdef __APPLE__
    if (errno == 0) {
        LOG(2, "Allocate test GC memory pool (%li bytes): mmap returned %p (Success)\n",
            gc.pool_size + 2 * BOUNDARY_SIZE,
            POOL_OFFSET(gc.pool)
        );
    }
    else {
        LOG(2, "Allocate test GC memory pool (%li bytes): mmap returned %p (%s)\n",
            gc.pool_size + 2 * BOUNDARY_SIZE,
            POOL_OFFSET(gc.pool),
            strerror(errno)
        );
    }
#else
    LOG(2, "Allocate test GC memory pool (%li bytes): mmap returned %p (%s)\n",
        gc.pool_size + 2 * BOUNDARY_SIZE,
        POOL_OFFSET(gc.pool),
        strerror(errno)
    );
#endif

    assert(errno == 0);

    LOG(3,  "memset %#02x at %p for %i bytes\n", FREE, gc.pool, gc.pool_size);
    memset(gc.pool, BOUNDARY, BOUNDARY_SIZE);
    memset(gc.pool + BOUNDARY_SIZE, FREE, gc.pool_size);
    memset(gc.pool + gc.pool_size + BOUNDARY_SIZE, BOUNDARY, BOUNDARY_SIZE);

    gc.pool_free = gc.pool + BOUNDARY_SIZE;

    if (gc.test_dump) {
        gc_pool_dump();
    }
#endif // GC_TEST

    gc.initialized = true;

#ifdef GC_PTHREAD
    if (pthread_mutex_unlock(&gc_init_mutex) != 0) {
        PANIC("Cannot unlock mutex");
    }
#endif // GC_PTHREAD
}

void gc_teardown(void) {
    LOG(2, "GC Teardown\n");

#ifdef GC_TEST
    if (gc.test_final_run) {
        // no blocks are reachable anymore
        llvm_gc_root_chain = NULL;
        gc_run(); // we don't run the gc in non test mode as the OS will free all remaining memory for us anyway
    }

    if (gc.test_dump) {
        gc_pool_dump();
    }

    assert(munmap((void *)gc.pool, gc.pool_size + 2 * BOUNDARY_SIZE) == 0);
#endif // GC_TEST

    char *gc_print_stats_env = getenv("GC_PRINT_STATS");
    if (gc_print_stats_env && strcmp(gc_print_stats_env, "1") == 0) {
        gc_print_statistics();
    }
}

static inline void gc_free(GcBlock *block) {
    void *object = GC_OBJECT(block);

    if (block->callbacks && block->callbacks->free) {
#ifdef GC_LOGS_STABLE
        LOG(2, "    "COLOR_START_BLUE"%p"COLOR_END": recursive free(object at "COLOR_START_BLUE"%p"COLOR_END")\n",
            POOL_OFFSET(block), POOL_OFFSET(object));
#else // GC_LOGS_STABLE
        LOG(2, "    "COLOR_START_BLUE"%p"COLOR_END": recursive free(object at "COLOR_START_BLUE"%p"COLOR_END") @ %p\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->callbacks->free);
#endif
        block->callbacks->free(object);
    }

    gc.free_count++;
    gc.total_free_sz += GC_BLOCK_SIZE + block->data_size;
    gc.current_alloc_sz -= GC_BLOCK_SIZE + block->data_size;
    gc.object_free_sz += block->data_size;
    gc.current_object_alloc_sz -= block->data_size;

#ifdef GC_TEST
    if (gc.test_dump_color) {
        block->next = gc.freed_blocks_chain;
        gc.freed_blocks_chain = block;
    }

    LOG(3,  "      memset %#02x at %p for %li bytes\n", FREED, block, GC_BLOCK_SIZE + block->data_size);
    memset(GC_OBJECT(block), FREED, block->data_size);
#else // GC_TEST
    free(block);
#endif // GC_TEST
}

void gc_run(void) {
    if (!gc.enable) {
        return;
    }

#ifdef GC_PTHREAD
    if (pthread_mutex_lock(&gc.lock) != 0) {
        PANIC("Cannot lock mutex");
    }
    LOG(3, "lock acquired\n");
#endif // GC_PTHREAD

    gc.execution_count++;

    LOG(2, "Start GC [%i]\n", gc.execution_count);
    if (gc.blocks_chain == NULL) {
        LOG(2, "no allocated blocks\n");
#ifdef GC_PTHREAD
        if (pthread_mutex_unlock(&gc.lock) != 0) {
            PANIC("Cannot unlock mutex");
        }
        LOG(3, "lock released\n");
#endif // GC_PTHREAD
        return;
    }

    LOG(2, "Phase: init.\n");
    GcBlock *block = gc.blocks_chain;
    while (block) {
        if (block->state != Owned) {
            block->state = Unreachable;
        }
#ifdef GC_LOGS
#ifdef GC_TEST
        gc_log(2, "gc_run", __LINE__, "  block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s'): %s\n",
            POOL_OFFSET(block),
            POOL_OFFSET(GC_OBJECT(block)),
            block->name,
            state_to_char(block->state)
        );
#else // GC_TEST
        gc_log(2, "gc_run", __LINE__, "  block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END"): %s\n",
            POOL_OFFSET(block),
            POOL_OFFSET(GC_OBJECT(block)),
            state_to_char(block->state)
        );
#endif // GC_TEST
#endif // GC_LOGS
        block = block->next;
    }

    LOG(2, "Phase: mark\n");
    LlvmStackFrame *frame = llvm_gc_root_chain;
#ifdef GC_LOGS
    for (int frame_idx = 0; frame; frame_idx++) {
#else
    while (frame) {
#endif // GC_LOGS
        LOG(2, "  frame %i (%i roots):\n", frame_idx, frame->map->num_roots);

        for (int32_t root_idx = 0; root_idx < frame->map->num_roots; root_idx++) {
            if (frame->roots[root_idx]) {
                LOG(2, "    root %i:\n", root_idx);
                gc_mark(frame->roots[root_idx]);
            }
            else {
                LOG(2, "    root %i: skipped (null)\n", root_idx);
            }
        }

        frame = frame->next;
    }

#ifdef GC_LOGS
    int run_count = 0;
#endif // GC_LOGS
    while (true) {
        LOG(2, "Phase: sweep (%i)\n", run_count);
        int freed = 0;
        GcBlock *prev = NULL;
        block = gc.blocks_chain;
        while (block) {
            if (block->state == Unreachable) {
                if (block == gc.blocks_chain) {
                    gc.blocks_chain = block->next;
                }
                else {
                    assert(prev != NULL);
                    prev->next = block->next;
                }
                GcBlock *next = block->next;
#ifdef GC_TEST
                LOG(1,  "  freeing block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END", size: %li: '%s')\n",
                    POOL_OFFSET(block), POOL_OFFSET(GC_OBJECT(block)), block->data_size, block->name);
#else
                LOG(1,  "  freeing block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END", size: %li)\n",
                    POOL_OFFSET(block), POOL_OFFSET(GC_OBJECT(block)), block->data_size);
#endif
                gc_free(block);
                block = next;
                freed++;
            }
            else {
#ifdef GC_TEST
                LOG(1,  "  keeping block "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END", size: %li: '%s'): %s\n",
                    POOL_OFFSET(block),
                    POOL_OFFSET(GC_OBJECT(block)),
                    block->data_size,
                    block->name,
                    state_to_char(block->state)
                );
#else // GC_TEST
                LOG(1,  "  keeping block "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END", size: %li): %s\n",
                    POOL_OFFSET(block),
                    POOL_OFFSET(GC_OBJECT(block)),
                    block->data_size,
                    state_to_char(block->state)
                );
#endif // GC_TEST
                prev = block;
                block = block->next;
            }
        }
        if (freed == 0) {
            break;
        }
        freed = 0;
#ifdef GC_LOGS
        run_count++;
#endif // GC_LOGS
    }

#ifdef GC_PTHREAD
    if (pthread_mutex_unlock(&gc.lock) != 0) {
        PANIC("Cannot unlock mutex");
    }
    LOG(3, "lock released\n");
#endif // GC_PTHREAD
}

void gc_mark(void *object) {
    GcBlock *block = GC_BLOCK(object);

#ifdef GC_TEST
    GcBlock *current_block = gc.blocks_chain;
    while (current_block) {
        if (current_block == block) {
            goto found;
        }
        current_block = current_block->next;
    }
    PANIC_ARGS("unmanaged block "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END")",
        POOL_OFFSET(block), POOL_OFFSET(object));
    found:
#endif // GC_TEST

#ifdef GC_LOGS
#ifdef GC_TEST
    LOG(2, "      mark %s block "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s')\n",
        state_to_char(block->state), POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_TEST
    LOG(2, "      mark %s block "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END")\n",
        state_to_char(block->state), POOL_OFFSET(block), POOL_OFFSET(object));
#endif // GC_TEST
#endif // GC_LOGS

    if (block->state == Reachable) {
        return;
    }
    block->state = Reachable;

    if (block->callbacks && block->callbacks->mark) {
#ifdef GC_TEST
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark(object at "COLOR_START_GREEN"%p"COLOR_END": '%s')\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_TEST
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark(object at "COLOR_START_GREEN"%p"COLOR_END")\n",
            POOL_OFFSET(block), POOL_OFFSET(object));
#endif // GC_TEST
        block->callbacks->mark(object);
    }
#ifdef GC_LOGS
    else {
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": skip recursive mark(object at "COLOR_START_GREEN"%p"COLOR_END"): no mark callback\n",
            POOL_OFFSET(block), POOL_OFFSET(object));
    }
#endif // GC_LOGS
}

void* gc_malloc(size_t data_size, size_t align, GcCallbacks *callbacks) {
    assert(gc.initialized);

#ifdef GC_PTHREAD
    if (pthread_mutex_lock(&gc.lock) != 0) {
        PANIC("Cannot lock mutex");
    }
    LOG(3, "lock acquired\n");
#endif // GC_PTHREAD

    LOG(2, "alloc %li bytes, align %li\n", data_size, align);
    gc_run();

    size_t alloc_size = GC_BLOCK_SIZE + data_size;

#ifdef GC_TEST
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
    LOG(3,  "memset %#02x at %p for %li bytes\n", ALLOCATED, block, alloc_size);
    memset(block, ALLOCATED, alloc_size);

    block->name = "";
#else // GC_TEST
    GcBlock *block = malloc(alloc_size);
    assert(block != NULL);
#endif // GC_TEST

    void *object = GC_OBJECT(block);
    assert((uintptr_t)object % align == 0);

    block->state = Unreachable;
    block->data_size = data_size;
    block->next = gc.blocks_chain;
    block->callbacks = callbacks;
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

    LOG(1,  "allocated block of size %li at "COLOR_START_BLUE"%p"COLOR_END", returning object of size %li at "COLOR_START_BLUE"%p"COLOR_END"(+%li)\n",
        alloc_size,
        POOL_OFFSET(block),
        data_size,
        POOL_OFFSET(object),
        (uint8_t *)object - (uint8_t *)block
    );

#ifdef GC_PTHREAD
    if (pthread_mutex_unlock(&gc.lock) != 0) {
        PANIC("Cannot unlock mutex");
    }
    LOG(3, "lock released\n");
#endif // GC_PTHREAD

    return object;
}

void gc_take_ownership(void *object) {
    GcBlock *block = GC_BLOCK(object);
#ifdef GC_TEST
    LOG(2, "mark block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s') as owned\n",
        POOL_OFFSET(block), POOL_OFFSET(object), block->name );
#else
    LOG(2, "mark block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END") as owned\n",
        POOL_OFFSET(block), POOL_OFFSET(object));
#endif // GC_TEST
    block->state = Owned;
}

void gc_set_callbacks(void *object, GcCallbacks *callbacks) {
    GcBlock *block = GC_BLOCK(object);

#ifdef GC_TEST
#ifdef GC_LOGS_STABLE
    LOG(2, "set callback of block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s')\n",
        POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_LOGS_STABLE
    LOG(2, "set callback of block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s') to %p\n",
        POOL_OFFSET(block), POOL_OFFSET(object), block->name, callbacks);
#endif // GC_LOGS_STABLE
#else // GC_TEST
#ifdef GC_LOGS_STABLE
    LOG(2, "set callback of block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END")\n",
        POOL_OFFSET(block), POOL_OFFSET(object));
#else // GC_LOGS_STABLE
    LOG(2, "set callback of block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END") to %p\n",
        POOL_OFFSET(block), POOL_OFFSET(object), callbacks);
#endif // GC_LOGS_STABLE
#endif // GC_TEST

    assert(callbacks != NULL);

    block->callbacks = callbacks;
}

void gc_release_ownership(void *object) {
    GcBlock *block = GC_BLOCK(object);

#ifdef GC_TEST
    LOG(2, "mark block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s') as unreachable\n",
        POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_TEST
    LOG(2, "mark block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END") as unreachable\n",
        POOL_OFFSET(block), POOL_OFFSET(object) );
#endif // GC_TEST

    block->state = Unreachable;
}

void gc_mark_managed(void *object) {
    GcBlock *block = GC_BLOCK(object);

#ifdef GC_TEST
    LOG(2, "      mark %s block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END": '%s') as reachable\n",
        state_to_char(block->state), POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_TEST
    LOG(2, "      mark %s block at "COLOR_START_BLUE"%p"COLOR_END" (object at "COLOR_START_GREEN"%p"COLOR_END") as reachable\n",
        state_to_char(block->state), POOL_OFFSET(block), POOL_OFFSET(object));
#endif // GC_TEST

    block->state = Reachable;

    if (block->callbacks && block->callbacks->mark) {
#if GC_TEST
#ifdef GC_LOGS_STABLE
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END": '%s')\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_LOGS_STABLE
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END": '%s') @ %p\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->name, block->callbacks->mark);
#endif // GC_LOGS_STABLE
#else // GC_TEST
#ifdef GC_LOGS_STABLE
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END")\n",
            POOL_OFFSET(block), POOL_OFFSET(object));
#else // GC_LOGS_STABLE
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END") @ %p\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->callbacks->mark);
#endif // GC_LOGS_STABLE
#endif // GC_TEST
        block->callbacks->mark(object);
    }
#ifdef GC_LOGS
    else {
#if GC_TEST
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": skip recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END": '%s'): no mark callback\n",
            POOL_OFFSET(block), POOL_OFFSET(object), block->name);
#else // GC_TEST
        LOG(2, "        "COLOR_START_BLUE"%p"COLOR_END": skip recursive mark (object at "COLOR_START_GREEN"%p"COLOR_END"): no mark callback\n",
            POOL_OFFSET(block), POOL_OFFSET(object));
#endif // GC_TEST
    }
#endif // GC_LOGS
}

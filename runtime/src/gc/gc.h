#include <stdlib.h>

typedef struct GcCallbacks {
    void (*mark)(void *);
    void (*free)(void *);
} GcCallbacks;

void* gc_malloc(size_t data_size, size_t align, GcCallbacks *callbacks);

void gc_init();
void gc_run();
void gc_teardown();
void gc_print_statistics();

void gc_mark(void *object);

void gc_set_callbacks(void *object, GcCallbacks *callbacks);

#ifdef GC_TEST
void gc_set_object_name(void *object, char *name);
void gc_pool_dump();
#endif // #ifdef GC_TEST

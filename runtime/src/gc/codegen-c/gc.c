// gc.c
#ifndef GC_H_INLINE
#define GC_PRIVATE
#include "../gc.h"
#endif

void gc_init(void) {

}

void gc_teardown(void) {

}

void* gc_malloc(size_t data_size, size_t align, GcCallbacks *callbacks) {
    UNUSED(align);
    UNUSED(callbacks);
    return malloc(data_size);
}

void gc_mark_managed(void *object) {
    UNUSED(object);
}

void gc_take_ownership(void *object) {
    UNUSED(object);
}
void gc_release_ownership(void *object) {
    UNUSED(object);
}

void gc_set_callbacks(void *object, GcCallbacks *callbacks) {
    UNUSED(object);
    UNUSED(callbacks);
}


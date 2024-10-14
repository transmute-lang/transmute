#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct HashMap_String__u64 HashMap_String__u64;

typedef struct Str {
  uint8_t *inner;
  uintptr_t len;
  uintptr_t capacity;
  bool dropped;
} Str;

typedef struct Inner {
  struct Str string;
  struct HashMap_String__u64 *map;
} Inner;

typedef struct Outer {
  struct Inner inner;
} Outer;

/**
 *
 * # Safety
 * Safe under the same conditions as `CStr::from_ptr()`.
 */
struct Str *str_new_cstr(const char *cstr);

void str_println(struct Str *s);

struct Str *str_new_static(uint8_t *buf, uintptr_t len, uintptr_t capacity);

void outer_add(struct Outer *outer, struct Str *s, uint64_t i);

struct Outer *outer_new(void);

extern uint8_t *gc_malloc(uintptr_t size, uintptr_t align, bool collectable);

extern void gc_set_collectable(const uint8_t *ptr, bool collectable, void (*collect_fn)(uint8_t*));

extern void rust_print(const char *what);

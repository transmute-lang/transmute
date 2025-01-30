
typedef struct GcArrayElement {
    struct GcPointeeLayout  *layout;
} GcArrayElement;

typedef struct GcStructField {
    size_t                  offset;
    struct GcPointeeLayout *layout;
} GcStructField;

typedef union GcPointeeKind {
    GcArrayElement          array_element;
    GcStructField           struct_fields[0];
} GcPointeeKind;

typedef enum GcPointeeKindTag {
    Struct  = 0,
    Array   = 1,
    Managed = 2,
} GcPointeeKindTag;

typedef struct GcPointeeLayout {
    GcPointeeKindTag        tag;
    size_t                  count;
    GcPointeeKind           pointee;
} GcPointeeLayout;


void* gc_malloc(size_t data_size, size_t align);

void gc_init();
void gc_run();
void gc_teardown();
void gc_print_statistics();

#ifdef GC_TEST
void gc_pool_dump();
#endif // #ifdef GC_TEST

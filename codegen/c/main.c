#include <stdio.h>
#include <stdlib.h>

#define UNUSED(v) ((void)v)

static void *frames = NULL;

typedef struct {
    void *parent;

    union {
        struct {
            int *i;
        };

        void *pointers[2];
    };
} f2__frame;

int *f2(void) {
    // prelude
    f2__frame *me = frames;

    me->i = malloc(sizeof(int));
    *me->i = 666;

    return me->i;
}

typedef struct {
    void *parent;

    union {
        struct {
            int *i;
        };

        void *pointers[2];
    };
} f1__frame;

int *f1(void) {
    // prelude
    f1__frame *me = frames;

    // call
    frames = &(f2__frame){.parent = me, .pointers = {0}};
    me->i = f2();
    frames = me;

    return me->i;
}

typedef struct {
    void *parent;

    union {
        struct {
            int *i;
        };

        void *pointers[2];
    };
} main__frame;

int main(int argc, char **argv) {
    // main prelude
    UNUSED(argc);
    UNUSED(argv);
    frames = &(main__frame){0};

    // prelude
    main__frame *me = frames;

    frames = &(f1__frame){.parent = me, .pointers = {0}};
    me->i = f1();
    frames = me;

    printf("%d\n", *me->i);
    return 0;
}

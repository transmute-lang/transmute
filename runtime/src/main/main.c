#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "main.h"
#include "../gc/gc.h"

void _TM0_F4main0(void);

static Args args = {0};

int main(int argc, char **argv) {
    gc_init();

    args.argc = argc;
    args.argv = argv;

    _TM0_F4main0();

    gc_teardown();

    return 0;
}

Args *get_c_args(void) {
    return &args;
}
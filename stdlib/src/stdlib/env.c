#include <string.h>
#include <stdio.h>

#include "bindings.h"
#include "../../../runtime/src/gc/gc.h"
#include "../../../runtime/src/main/main.h"

static List *args = NULL;

List *_TM0_N3stdN3envF4args0() {
    if (args == NULL) {
        args = stdlib_list_new();
        gc_take_ownership(args); // to make sure it's not GC-ed

        Args *c_args = get_c_args();

        for (int i = 0; i < c_args->argc; i++) {
//            printf("argc[%i] = %s\n", i, c_args->argv[i]);

            Str *arg = tmc_stdlib_string_new((const uint8_t *)c_args->argv[i], strlen(c_args->argv[i]));
            gc_take_ownership(arg); // to make sure it's not GC-ed

            stdlib_list_push(args, arg);
            gc_take_ownership(args); // to make sure it's not GC-ed

            gc_release_ownership(arg); // it's in the list, it can now be GC-ed
        }
    }

//printf("returning args\n");
    return args;
}
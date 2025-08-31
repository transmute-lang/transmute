#include <stdio.h>

#include "bindings.h"

void _TM0_N3stdN3strF5print1sN3stdN3str6string(Str *str) {
    printf("%.*s\n", (int)str->len, (char *)str->ptr);
}

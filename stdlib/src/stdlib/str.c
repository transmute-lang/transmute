#include <stdio.h>

#include "bindings.h"

// print(string) -> _TM0_5print1s
void _TM0_5print1s(Str *str) {
    printf("%.*s\n", (int)str->len, (char *)str->ptr);
}

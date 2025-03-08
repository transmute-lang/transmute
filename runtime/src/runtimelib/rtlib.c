#include <stdio.h>

#include "../gc/gc.h"
#include "../../../stdlib/bindings/transmute-stdlib.h"

// print(number) -> _TM0_5print1n
void _TM0_5print1n(int64_t a) {
#ifdef __APPLE__
    printf("%lli\n", a);
#else
    printf("%li\n", a);
#endif
}

// print(boolean) -> _TM0_5print1b
void _TM0_5print1b(int8_t b) {
    if (b) {
        printf("true\n");
    } else {
        printf("false\n");
    }
}

// print(string) -> _TM0_5print1s
void _TM0_5print1s(Str *str) {
    printf("%.*s\n", (int)str->len, (char *)str->ptr);
}

void _TM0_8gc_stats0(void) {
    gc_print_statistics();
}

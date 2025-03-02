#include "../gc/gc.h"

// print(number) -> _TM0_5print1n
void _TM0_5print1n(int64_t a) {
    printf("%li\n", a);
}

// print(boolean) -> _TM0_5print1b
void _TM0_5print1b(int8_t b) {
    if (b) {
        printf("true\n");
    } else {
        printf("false\n");
    }
}

void _TM0_8gc_stats0() {
    gc_print_statistics();
}
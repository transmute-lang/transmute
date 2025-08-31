#include <stdio.h>
#include <stdint.h>

void _TM0_N3stdN7numbersF5print1n(int64_t a) {
#ifdef __APPLE__
    printf("%lli\n", a);
#else
    printf("%li\n", a);
#endif
}

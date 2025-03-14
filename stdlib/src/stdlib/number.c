#include <stdio.h>
#include <stdint.h>

// print(number) -> _TM0_5print1n
void _TM0_5print1n(int64_t a) {
#ifdef __APPLE__
    printf("%lli\n", a);
#else
    printf("%li\n", a);
#endif
}

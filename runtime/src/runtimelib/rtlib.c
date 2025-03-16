#include "../gc/gc.h"

// gc_stat() -> _TM0_8gc_stats0
void _TM0_8gc_stats0(void) {
    gc_print_statistics();
}

// gc_run() -> _TM0_6gc_run0
void _TM0_6gc_run0(void) {
    gc_run();
}

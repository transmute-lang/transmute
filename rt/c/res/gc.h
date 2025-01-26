
void gc_init();
void gc_teardown();
void gc_print_statistics();

#ifdef GC_TEST
void gc_pool_dump();
#endif // #ifdef GC_TEST

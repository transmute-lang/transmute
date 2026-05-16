// main-post.c
int main(int argc, char **argv)
{
    //not actually always unused, but warning must be silenced
    UNUSED(frames);

    // save args
    args.argc = argc;
    args.argv = argv;

    gc_init();

    // call transmute main
    _TM0_F4main0(NULL);

    gc_teardown();

    return 0;
}


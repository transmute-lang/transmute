let main(n: number): number {
    if n < 2 {
        ret n;
    }
    main(n - 1) + main(n - 2);
}
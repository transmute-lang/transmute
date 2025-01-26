fn main() {
    #[cfg(feature = "test-wrapper")]
    {
        let crate_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();

        std::fs::remove_dir_all("./bindings").ok();
        std::fs::create_dir_all("./bindings").unwrap();

        cbindgen::Builder::new()
            .with_crate(crate_dir)
            .with_language(cbindgen::Language::C)
            .exclude_item("LlvmStackFrame")
            .exclude_item("LlvmFrameMap")
            //.with_include("../llvm.h")
            .generate()
            .unwrap()
            .write_to_file("bindings/rustrt.h");
    }

    println!("cargo::rustc-link-lib=tmcrt");
    println!("cargo::rustc-link-search=target");
}

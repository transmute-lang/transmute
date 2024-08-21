use std::{env, fs};

fn main() {
    // fixme what about cross compilation?
    let files = cc::Build::new().file("res/main.c").compile_intermediates();

    let objects = format!(
        r#"
        pub fn get_main() -> &'static[u8] {{
            include_bytes!("{}")
        }}
    "#,
        files[0].display()
    );

    fs::write(
        format!("{}/objects.rs", env::var("OUT_DIR").unwrap()),
        objects,
    )
    .unwrap();

    println!("cargo::rerun-if-changed=res/main.c");
}

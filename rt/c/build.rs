use std::env::current_dir;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

fn main() {
    let mut llvm_link_command = Command::new("llvm-link");
    llvm_link_command
        .arg("-o")
        .arg(format!("{}/crt.bc", env::var("OUT_DIR").unwrap()));

    let res_dir = current_dir().unwrap().join("res");
    for dir_entry in fs::read_dir(&res_dir).unwrap() {
        let c_file_name = dir_entry
            .expect("dir entry exists")
            .file_name()
            .to_str()
            .unwrap()
            .to_string();

        let src = res_dir.join(&c_file_name);
        let dst = PathBuf::from(format!(
            "{}/{}.ll",
            env::var("OUT_DIR").unwrap(),
            c_file_name
        ));

        println!("cargo::rerun-if-changed={}", src.display());
        compile_to_llvm_ir(&src, &dst);
        llvm_link_command.arg(dst.as_os_str());
    }

    let output = llvm_link_command
        .output()
        .expect("can generate LLVM IR for other.c");
    if !output.status.success() {
        panic!("{}", String::from_utf8(output.stderr).unwrap());
    }

    let objects = format!(
        r#"
        pub fn get_crt() -> &'static [u8] {{
            include_bytes!("{}/crt.bc")
        }}
    "#,
        env::var("OUT_DIR").unwrap()
    );

    fs::write(
        format!("{}/include.rs", env::var("OUT_DIR").unwrap()),
        objects,
    )
    .unwrap();
}

fn compile_to_llvm_ir(src: &Path, dst: &Path) {
    let output = Command::new("clang")
        .arg("-S")
        .arg("-emit-llvm")
        .arg("-o")
        .arg(dst.as_os_str())
        .arg(src.as_os_str())
        .output()
        .unwrap_or_else(|_| panic!("could not generate LLVM IR for {}", src.display()));
    if !output.status.success() {
        panic!("{}", String::from_utf8(output.stderr).unwrap());
    }
}

use std::env::current_dir;
use std::fs::File;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

fn main() {
    build_llvm_bitcode();
    build_c_sources();

    fs::write(
        format!("{}/include.rs", env::var("OUT_DIR").unwrap()),
        format!(
            r#"
            pub fn get_llvm_runtime() -> &'static [u8] {{
                include_bytes!("{out}/runtime.bc")
            }}

            pub fn get_c_pre() -> &'static [u8] {{
                include_bytes!("{out}/pre.c")
            }}

            pub fn get_c_post() -> &'static [u8] {{
                include_bytes!("{out}/post.c")
            }}
        "#,
            out = env::var("OUT_DIR").unwrap(),
        ),
    )
    .unwrap();
}

fn build_llvm_bitcode() {
    let mut llvm_link_command = Command::new("llvm-link");
    llvm_link_command
        .arg("-o")
        .arg(format!("{}/runtime.bc", env::var("OUT_DIR").unwrap()));

    let src_dir = current_dir().unwrap().join("src");

    #[cfg(not(feature = "gc-functions"))]
    let dirs = ["gc/codegen-llvm", "main/codegen-llvm", "tmc/codegen-llvm"];
    #[cfg(feature = "gc-functions")]
    let dirs = [
        "gc/codegen-llvm",
        "main/codegen-llvm",
        "tmc/codegen-llvm",
        "runtimelib",
    ];

    for d in dirs {
        let res_dir = src_dir.join(d);
        for dir_entry in fs::read_dir(&res_dir).unwrap() {
            let c_file_name = dir_entry
                .expect("dir entry exists")
                .file_name()
                .to_str()
                .unwrap()
                .to_string();

            let src = res_dir.join(&c_file_name);
            let extension = src.extension().unwrap();
            if extension.eq("c") {
                let dst = PathBuf::from(format!(
                    "{}/{}.ll",
                    env::var("OUT_DIR").unwrap(),
                    c_file_name
                ));

                println!("cargo::rerun-if-changed={}", src.display());
                compile_to_llvm_ir(&src, &dst);
                llvm_link_command.arg(dst.as_os_str());
            } else if extension.eq("h") {
                println!("cargo::rerun-if-changed={}", src.display());
            }
        }
    }

    let output = llvm_link_command.output().expect("can generate LLVM IR");
    if !output.status.success() {
        panic!("{}", String::from_utf8_lossy(&output.stderr));
    }
}

#[cfg(feature = "gc-logs")]
const GC_LOGS: [&str; 2] = ["-D", "GC_LOGS"];

#[cfg(not(feature = "gc-logs"))]
const GC_LOGS: [&str; 0] = [];

#[cfg(feature = "gc-logs-stable")]
const GC_LOGS_STABLE: [&str; 2] = ["-D", "GC_LOGS_STABLE"];

#[cfg(not(feature = "gc-logs-stable"))]
const GC_LOGS_STABLE: [&str; 0] = [];

#[cfg(feature = "gc-logs-colors")]
const GC_LOGS_COLOR: [&str; 2] = ["-D", "GC_LOGS_COLOR"];

#[cfg(not(feature = "gc-logs-colors"))]
const GC_LOGS_COLOR: [&str; 0] = [];

#[cfg(feature = "gc-test")]
const GC_TEST: [&str; 2] = ["-D", "GC_TEST"];

#[cfg(not(feature = "gc-test"))]
const GC_TEST: [&str; 0] = [];

#[cfg(feature = "gc-cc-dbg")]
const GC_DBG: [&str; 1] = ["-ggdb"];

#[cfg(not(feature = "gc-cc-dbg"))]
const GC_DBG: [&str; 0] = [];

#[cfg(feature = "gc-pthread")]
const GC_PTHREAD: [&str; 2] = ["-D", "GC_PTHREAD"];

#[cfg(not(feature = "gc-pthread"))]
const GC_PTHREAD: [&str; 0] = [];

fn compile_to_llvm_ir(src: &Path, dst: &Path) {
    let output = Command::new("clang")
        .arg("-S")
        .args(GC_TEST)
        .args(GC_LOGS)
        .args(GC_LOGS_STABLE)
        .args(GC_LOGS_COLOR)
        .args(GC_PTHREAD)
        .arg("-emit-llvm")
        .args(GC_DBG)
        .arg("-o")
        .arg(dst.as_os_str())
        .arg(src.as_os_str())
        .output()
        .unwrap_or_else(|_| panic!("could not generate LLVM IR for {}", src.display()));
    if !output.status.success() {
        panic!("{}", String::from_utf8(output.stderr).unwrap());
    }
}

fn build_c_sources() {
    let out_dir = env::var("OUT_DIR").unwrap();

    let mut buf = Vec::new();
    let pre_path = Path::new(&out_dir).join("pre.c");
    let mut pre = File::create(&pre_path).unwrap();

    #[cfg(not(feature = "stdlib"))]
    let source = [
        "src/main/codegen-c/header.c",
        "src/gc/gc.h",
        "src/main/args.h",
        "src/main/codegen-c/main-pre.c",
        "src/gc/codegen-c/gc.c",
        "src/tmc/codegen-c/tmc.c",
    ];

    #[cfg(feature = "stdlib")]
    let source = [
        "src/main/codegen-c/header.c",
        "src/gc/gc.h",
        "src/main/args.h",
        "src/main/codegen-c/main-pre.c",
        "src/gc/codegen-c/gc.c",
        "src/tmc/codegen-c/tmc.c",
        "../stdlib/src/stdlib/bindings.h",
    ];

    for f in source {
        println!("cargo::rerun-if-changed={}", f);
        File::open(f).unwrap().read_to_end(&mut buf).unwrap();
    }
    pre.write_all(&buf).unwrap();

    buf.clear();
    let post_path = Path::new(&out_dir).join("post.c");
    let mut post = File::create(&post_path).unwrap();
    let f = "src/main/codegen-c/main-post.c";
    println!("cargo::rerun-if-changed={}", f);
    File::open(f).unwrap().read_to_end(&mut buf).unwrap();
    post.write_all(&buf).unwrap();
}

use std::env::current_dir;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

fn main() {
    let mut llvm_link_command = Command::new("llvm-link");
    llvm_link_command
        .arg("-o")
        .arg(format!("{}/runtime.bc", env::var("OUT_DIR").unwrap()));

    let src_dir = current_dir().unwrap().join("src");

    #[cfg(not(feature = "gc-functions"))]
    let dirs = ["gc", "main", "tmc"];
    #[cfg(feature = "gc-functions")]
    let dirs = ["gc", "main", "tmc", "runtimelib"];

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

    let objects = format!(
        r#"
        pub fn get_runtime() -> &'static [u8] {{
            include_bytes!("{}/runtime.bc")
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

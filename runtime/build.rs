use std::env::current_dir;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

fn main() {
    // todo:ux parameterize llvm-link
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
            if !src.extension().unwrap().eq("c") {
                continue;
            }

            let dst = PathBuf::from(format!(
                "{}/{}.ll",
                env::var("OUT_DIR").unwrap(),
                c_file_name
            ));

            println!("cargo::rerun-if-changed={}", src.display());
            compile_to_llvm_ir(&src, &dst);
            llvm_link_command.arg(dst.as_os_str());
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
const GC_LOGS: &str = "-D GC_LOGS";

#[cfg(not(feature = "gc-logs"))]
const GC_LOGS: &str = "";

#[cfg(feature = "gc-stable-logs")]
const GC_STABLE_LOGS: &str = "-D GC_STABLE_LOGS";

#[cfg(not(feature = "gc-stable-logs"))]
const GC_STABLE_LOGS: &str = "";

#[cfg(feature = "gc-test")]
const GC_TEST: &str = "-D GC_TEST";

#[cfg(not(feature = "gc-test"))]
const GC_TEST: &str = "";

fn compile_to_llvm_ir(src: &Path, dst: &Path) {
    let output = Command::new("clang")
        .arg("-S")
        .arg(GC_TEST)
        .arg(GC_LOGS)
        .arg(GC_STABLE_LOGS)
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

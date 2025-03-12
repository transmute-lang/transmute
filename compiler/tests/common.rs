use std::env;
use std::path::PathBuf;
use std::process::Command;
use test_dir::{DirBuilder, TestDir};
use tmc::{compile_str, Options};

#[allow(unused_macros)]
macro_rules! exec {
    ($name:expr, $arg:expr) => {
        paste::paste! {
            #[test]
            fn [< test_ $name >]() {
                let test_dir = test_dir::DirBuilder::create(test_dir::TestDir::temp(), ".", test_dir::FileType::Dir);

                let stdlib_src = std::path::PathBuf::from(std::env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
                let stdlib_src = stdlib_src.join("src");

                let mut source = include_str!(concat!("../../examples/", $name, ".tm")).to_string();
                for entry in std::fs::read_dir(&stdlib_src).unwrap() {
                    let file = entry
                        .unwrap()
                        .file_name()
                        .to_str()
                        .unwrap()
                        .to_string();

                    let src = stdlib_src.join(&file);
                    if !src.extension().unwrap().eq("tm") {
                        continue;
                    }

                    // println!("Reading {}", src.display());

                    let src = std::fs::read_to_string(&src)
                        .map_err(|e| format!("Could not read {}: {}", src.display(), e)).unwrap();
                    source.push_str(&src);
                }

                let output = common::compile(
                    &source,
                    &test_dir
                )
                .arg($arg)
                .output()
                .unwrap();

                insta::assert_snapshot!(
                    format!("success:{}\nstdout:\n{}\n\nstderr:\n{}",
                        output.status.success(),
                        String::from_utf8(output.stdout).unwrap(),
                        String::from_utf8(output.stderr).unwrap()
                    )
                );
            }
        }
    };
}

#[allow(unused_macros)]
macro_rules! exec_test_example {
    ($name:expr, $arg:expr) => {
        paste::paste! {
            #[test]
            fn [< test_ $name >]() {
                let test_dir = test_dir::DirBuilder::create(test_dir::TestDir::temp(), ".", test_dir::FileType::Dir);

                let stdlib_src = std::path::PathBuf::from(std::env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
                let stdlib_src = stdlib_src.join("src");

                let mut source = include_str!(concat!("examples/", $name, ".tm")).to_string();
                for entry in std::fs::read_dir(&stdlib_src).unwrap() {
                    let file = entry
                        .unwrap()
                        .file_name()
                        .to_str()
                        .unwrap()
                        .to_string();

                    let src = stdlib_src.join(&file);
                    if !src.extension().unwrap().eq("tm") {
                        continue;
                    }

                    // println!("Reading {}", src.display());

                    let src = std::fs::read_to_string(&src)
                        .map_err(|e| format!("Could not read {}: {}", src.display(), e)).unwrap();
                    source.push_str(&src);
                }

                let output = common::compile(
                    &source,
                    &test_dir
                )
                .arg($arg)
                .output()
                .unwrap();

                insta::assert_snapshot!(
                    format!("success:{}\nstdout:\n{}\n\nstderr:\n{}",
                        output.status.success(),
                        String::from_utf8(output.stdout).unwrap(),
                        String::from_utf8(output.stderr).unwrap()
                    )
                );
            }
        }
    };
}

#[allow(unused_imports)]
pub(crate) use exec;

#[allow(unused_imports)]
pub(crate) use exec_test_example;

pub fn compile(src: &str, test_dir: &TestDir) -> Command {
    let bin_path = test_dir.path("a.out");

    let mut options = Options::default();
    let stdlib_path =
        PathBuf::from(env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
    options.set_stdlib_path(stdlib_path);

    match compile_str(src, &bin_path, &options) {
        Ok(_) => {
            let mut command = Command::new(bin_path);
            command.env("GC_LOG_LEVEL", "2");
            command.env("GC_TEST_POOL_SIZE", "16384");
            command.env("GC_PRINT_STATS", "1");
            command
        }
        Err(d) => {
            assert!(false, "{}", d);
            unreachable!()
        }
    }
}

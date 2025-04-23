use std::env;
use std::path::PathBuf;
use std::process::Command;
use test_dir::{DirBuilder, TestDir};
use tmc::{compile_inputs, Options};
use transmute_core::input::Input;

#[allow(unused_macros)]
macro_rules! exec {
    ($name:expr, $arg:expr) => {
        paste::paste! {
            #[test]
            fn [< test_ $name >]() {
                let test_dir = test_dir::DirBuilder::create(test_dir::TestDir::temp(), ".", test_dir::FileType::Dir);

                let mut stdlib_src = std::path::PathBuf::from(std::env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
                stdlib_src.push("src");
                stdlib_src.push("stdlib.tm");

                let mut inputs = vec![
                    transmute_core::input::Input::core(),
                    transmute_core::input::Input::try_from(std::path::PathBuf::from(concat!("../examples/", $name, ".tm"))).unwrap(),
                    transmute_core::input::Input::try_from(stdlib_src).unwrap()
                ];

                #[cfg(feature = "gc-functions")]
                inputs.push(transmute_core::input::Input::from(("gc-functions", include_str!("../src/gc-functions.tm"))));

                let output = common::compile(
                    inputs,
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

                let mut stdlib_src = std::path::PathBuf::from(std::env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
                stdlib_src.push("src");
                stdlib_src.push("stdlib.tm");

                let mut inputs = vec![
                    transmute_core::input::Input::core(),
                    transmute_core::input::Input::try_from(std::path::PathBuf::from(concat!("tests/examples/", $name, ".tm"))).unwrap(),
                    transmute_core::input::Input::try_from(stdlib_src).unwrap()
                ];

                #[cfg(feature = "gc-functions")]
                inputs.push(transmute_core::input::Input::from(("gc-functions", include_str!("../src/gc-functions.tm"))));

                let output = common::compile(
                    inputs,
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

pub fn compile(inputs: Vec<Input>, test_dir: &TestDir) -> Command {
    let bin_path = test_dir.path("a.out");

    let mut options = Options::default();
    let stdlib_path =
        PathBuf::from(env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is not set"));
    options.set_stdlib_path(stdlib_path);

    match compile_inputs(inputs, &bin_path, &options) {
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

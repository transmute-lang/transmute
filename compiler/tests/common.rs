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

                let output = common::compile(
                    include_str!(concat!("../../examples/", $name, ".tm")),
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

pub fn compile(src: &str, test_dir: &TestDir) -> Command {
    let bin_path = test_dir.path("a.out");

    // println!("{}", bin_path.display());
    let options = Options::default();

    match compile_str(src, &bin_path, &options) {
        Ok(_) => {
            let mut command = Command::new(bin_path);
            command.env("GC_LOG_LEVEL", "2");
            command.env("GC_TEST_POOL_SIZE", "4098");
            command
        }
        Err(d) => {
            assert!(false, "{}", d);
            unreachable!()
        }
    }
}

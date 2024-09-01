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

                assert!(
                    output.status.success(),
                    "{}",
                    String::from_utf8(output.stderr).unwrap()
                );

                insta::assert_snapshot!(String::from_utf8(output.stdout).unwrap());
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
        Ok(_) => Command::new(bin_path),
        Err(d) => {
            assert!(false, "{}", d);
            unreachable!()
        }
    }
}

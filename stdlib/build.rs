#[cfg(feature = "stdc")]
use std::env::current_dir;
#[cfg(feature = "stdc")]
use std::fs;

fn main() {
    #[cfg(feature = "stdc")]
    {
        let src_dir = current_dir().unwrap().join("src").join("stdlib");

        let mut cc = cc::Build::new();

        for dir_entry in fs::read_dir(&src_dir).unwrap() {
            let c_file_name = dir_entry
                .expect("dir entry exists")
                .file_name()
                .to_str()
                .unwrap()
                .to_string();

            let src = src_dir.join(&c_file_name);
            let extension = src.extension().unwrap();

            if extension.eq("c") {
                println!("cargo::rerun-if-changed={}", src.display());
                cc.file(&src);
            } else if extension.eq("h") {
                println!("cargo::rerun-if-changed={}", src.display());
            }
        }

        cc.compile("stdc");
    }
}

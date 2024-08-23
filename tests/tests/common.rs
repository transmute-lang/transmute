use std::process::Command;

pub fn compile(program: &str) -> Command {
    // todo should have a lib of compiler that can output binary
    let output = Command::new("cargo")
        .current_dir("..")
        .arg("run")
        .arg("--bin")
        .arg("tmc")
        .arg("--")
        .arg(format!("examples/{}.tm", program))
        .arg("-o")
        .arg(format!("target/{}", program))
        .output()
        .unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8(output.stderr).unwrap()
    );

    let mut command = Command::new(format!("target/{}", program));
    command.current_dir("..");
    command
}

use crate::common::compile;
use insta::assert_snapshot;

mod common;

#[test]
fn test_fibo_rec() {
    let output = compile("fibo_rec").arg("10").output().unwrap();

    assert!(
        output.status.success(),
        "{}",
        String::from_utf8(output.stderr).unwrap()
    );

    assert_snapshot!(String::from_utf8(output.stdout).unwrap());
}

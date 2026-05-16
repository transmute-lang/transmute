mod cli;

use crate::cli::CliConfig;
use colored::Colorize;
use serde::{Deserialize, Serialize};
use std::fmt::{Display, Formatter};
use std::process::{Command, Stdio, exit};
use std::{env, fs};

const TMC_BIN: &str = "./target/release/tmc";
const PROGRAM: &str = "./target/a.out";

#[derive(Serialize, Deserialize, Debug)]
struct Test {
    source: String,
    args: Vec<String>,
    status: i32,
    stdout: String,
    stderr: String,
}

#[derive(Serialize, Deserialize, Debug)]
struct Tests {
    tests: Vec<Test>,
}

fn main() {
    if !fs::exists(TMC_BIN).unwrap_or_default() {
        eprintln!("{TMC_BIN} not found. Are you running from project's root?");
        std::process::exit(1);
    }

    let config = cli::parse_args();

    let mut reports = Vec::new();
    let tests =
        toml::from_str::<Tests>(&fs::read_to_string("e2e-tests/tests.toml").unwrap()).unwrap();

    for (idx, test) in tests.tests.iter().enumerate() {
        if config.kinds.contains(&Kind::Llvm) {
            if let Some(report) = test_llvm(&config, test) {
                let _ = fs::rename(
                    PROGRAM,
                    format!(
                        "./target/{}-{}",
                        test.source.split("/").last().unwrap(),
                        Kind::Llvm
                    ),
                );
                reports.push((idx, Kind::Llvm, report))
            } else {
                let _ = fs::remove_file(PROGRAM);
            }
        }

        if config.kinds.contains(&Kind::C) {
            if let Some(report) = test_c(&config, test) {
                let _ = fs::rename(
                    PROGRAM,
                    format!(
                        "./target/{}-{}",
                        test.source.split("/").last().unwrap(),
                        Kind::C
                    ),
                );
                reports.push((idx, Kind::C, report))
            } else {
                let _ = fs::remove_file(PROGRAM);
            }
        }
    }

    println!();
    for (idx, kind, report) in &reports {
        println!("test {}::{kind} failed:", tests.tests[*idx].source);
        println!("{}\n", report);
    }

    if !reports.is_empty() {
        exit(1);
    }
}

fn test_llvm(config: &CliConfig, test: &Test) -> Option<Report> {
    print!("test {}::{} ... ", test.source, Kind::Llvm);
    let _ = fs::remove_file(PROGRAM);
    if compile_llvm(config, test) {
        exec(config, test)
    } else {
        println!("{}", "compilation failed".yellow());
        None
    }
}

fn compile_llvm(config: &CliConfig, test: &Test) -> bool {
    Command::new(TMC_BIN)
        .args([&test.source, "-o", PROGRAM])
        .stdout(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .stderr(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .status()
        .unwrap_or_else(|_|panic!("Could not compile {}", test.source))
        .success()
}

fn test_c(config: &CliConfig, test: &Test) -> Option<Report> {
    print!("test {}::{} ... ", test.source, Kind::C);
    let _ = fs::remove_file(PROGRAM);
    if compile_c(config, test) {
        exec(config, test)
    } else {
        println!("{}", "compilation failed".yellow());
        None
    }
}

fn compile_c(config: &CliConfig, test: &Test) -> bool {
    if !Command::new(TMC_BIN)
        .args([&test.source, "--c", "-o", "./target/a.c"])
        .stdout(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .stderr(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .status()
        .unwrap_or_else(|_| panic!("Could not compile {}", test.source))
        .success()
    {
        return false;
    }

    let stdlib_path = env::var("TRANSMUTE_STDLIB_PATH").expect("TRANSMUTE_STDLIB_PATH is set");
    Command::new("cc")
        .args([
            "-Wall",
            "-Wextra",
            "-Wpedantic",
            "-pedantic-errors",
            "-Wconversion",
            "--std=c17",
            "-ltransmute_stdlib",
            "./target/a.c",
            "-o",
            PROGRAM,
            "-L",
            &stdlib_path,
        ])
        .stdout(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .stderr(if config.verbose {
            Stdio::inherit()
        } else {
            Stdio::null()
        })
        .status()
        .unwrap_or_else(|_| panic!("Could not compile {}", test.source))
        .success()
}

fn exec(config: &CliConfig, test: &Test) -> Option<Report> {
    let res = Command::new(PROGRAM)
        .args(&test.args)
        .env("GC_ENABLE", if config.no_gc { "0" } else { "1" })
        .output()
        .unwrap_or_else(|_| panic!("Failed to execute {} program", test.source));

    if let Some(status) = res.status.code() {
        if status != test.status {
            println!("{}", "fail".red());
            Some(Report(format!(
                "expected to terminate with {} but was {}",
                test.status, status
            )))
        } else if res.stdout.as_slice() != test.stdout.as_bytes() {
            println!("{}", "fail".red());
            Some(Report(format!(
                "stdout does not match\nExpected:\n{}\nGot:\n{}",
                test.stdout,
                String::from_utf8_lossy(&res.stdout)
            )))
        } else if res.stderr.as_slice() != test.stderr.as_bytes() {
            println!("{}", "fail".red());
            Some(Report(format!(
                "stderr does not match\nExpected:\n{}\nGot:\n{}",
                test.stderr,
                String::from_utf8_lossy(&res.stderr)
            )))
        } else {
            println!("{}", "ok".green());
            None
        }
    } else {
        println!("{}", "fail".red());
        Some(Report(format!(
            "expected to terminate with {} but was interrupted",
            test.status,
        )))
    }
}

#[derive(Debug)]
struct Report(String);

impl Display for Report {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        self.0.fmt(f)
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone, Copy)]
enum Kind {
    Llvm,
    C,
}

impl Display for Kind {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            Kind::Llvm => write!(f, "llvm"),
            Kind::C => write!(f, "c"),
        }
    }
}

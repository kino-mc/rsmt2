//! Example of using a custom command for z3.

#[macro_use]
extern crate clap;

use rsmt2::prelude::*;

fn main() {
    let matches = clap_app!(myapp =>
        (version: "1.0")
        (about: "Example of using a custom command for z3")
        (@arg CMD: --z3_cmd +takes_value "Specifies a custom command to run z3")
        (@arg INPUT: "An optional smt2 file")
    )
    .get_matches();

    let file = matches.value_of("INPUT");
    let cmd = matches.value_of("CMD");

    if let Err(e) = run(file, cmd) {
        eprintln!("|===| Error");
        for line in e.to_string().lines() {
            eprintln!("| {}", line)
        }
        eprintln!("|===|")
    }
}

fn run(file: Option<&str>, cmd: Option<&str>) -> SmtRes<()> {
    if let Some(file) = file {
        let output = run_file(file, cmd)?;
        print!("{}", output);
        Ok(())
    } else {
        run_test(cmd)
    }
}

fn solver(cmd: Option<&str>) -> SmtRes<Solver<()>> {
    let cmd = cmd.unwrap_or_else(|| rsmt2::SmtStyle::Z3.cmd());
    SmtConf::z3(cmd).spawn(())
}

fn run_file(file: &str, cmd: Option<&str>) -> SmtRes<String> {
    use std::io::{BufRead, BufReader, Read, Write};

    let mut file_read = std::fs::OpenOptions::new().read(true).open(file)?;
    let mut content = String::with_capacity(103);

    file_read.read_to_string(&mut content)?;

    let mut solver = solver(cmd)?;

    solver.write(content.as_bytes())?;
    solver.flush()?;

    content.clear();

    let mut solver = BufReader::new(solver);

    assert!(content.is_empty());
    loop {
        if solver.read_line(&mut content)? == 0 {
            break;
        }
    }

    Ok(content)
}

fn run_test(cmd: Option<&str>) -> SmtRes<()> {
    let mut solver = solver(cmd)?;

    solver.declare_const("a", "Bool")?;
    solver.assert("(and a (not a))")?;

    if solver.check_sat()? {
        panic!("expected unsat, got sat")
    } else {
        println!("success")
    }

    Ok(())
}

#[test]
fn test_unknown_cmd() {
    assert_eq!(
        run_test(Some("z3_unknown_command"))
            .unwrap_err()
            .to_string(),
        "While spawning child process with z3_unknown_command"
    )
}

#[test]
fn test_rsc_test_smt2() {
    assert_eq!(
        run_file("rsc/test.smt2", Some("z3")).unwrap().trim(),
        "unsat"
    )
}

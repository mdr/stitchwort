//! Runs a program's `main` on the machine, for measuring it against
//! `stitchwort run` before stage 3 wires it into the CLI:
//!
//!   cargo run --release -p stitchwort-rt --example rt_run -- FILE.sw < input
//!   cargo run --release -p stitchwort-rt --example rt_run -- PROJECT-DIR Name.main < input
//!
//! Prints the output, and to standard error how long checking, lowering
//! and running took.

use std::io::Write;
use std::path::Path;
use std::process::ExitCode;
use std::rc::Rc;
use std::time::Instant;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    with_stack(1 << 30, move || run(&args))
}

fn run(args: &[String]) -> ExitCode {
    let start = Instant::now();
    let mut session = Session::new();
    let main = match args {
        [file] => {
            let path = Path::new(file);
            let text = std::fs::read_to_string(path).expect("read the file");
            let name = path.file_name().unwrap().to_string_lossy().to_string();
            session.include_in_folder(
                Rc::new(DiskFiles {
                    root: path.parent().unwrap().to_path_buf(),
                }),
                &name,
            );
            if let Err(e) = session.load(&name, &text) {
                eprintln!("doesn't check: {e:?}");
                return ExitCode::FAILURE;
            }
            session.main()
        }
        [dir, target] => {
            let dir = Path::new(dir);
            let name = dir.file_name().unwrap().to_string_lossy().to_string();
            let namespace = target.rsplit_once('.').map_or("", |(n, _)| n).to_string();
            if let Err(e) = session.load_project(
                &DiskFiles {
                    root: dir.to_path_buf(),
                },
                &name,
                &Target::Namespaces(vec![namespace]),
            ) {
                eprintln!("doesn't check: {e:?}");
                return ExitCode::FAILURE;
            }
            session.main_named(target, &name)
        }
        _ => {
            eprintln!("usage: rt_run FILE.sw | rt_run PROJECT-DIR Name.main");
            return ExitCode::FAILURE;
        }
    };
    let main = match main {
        Ok(main) => main,
        Err(e) => {
            eprintln!("{e:?}");
            return ExitCode::FAILURE;
        }
    };
    let checked = start.elapsed();
    let g = &session.elab.globals;
    let program = match stitchwort_rt::lower_main(g, session.elab.limits, main.term()) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{e:?}");
            return ExitCode::FAILURE;
        }
    };
    let lowered = start.elapsed();
    let limits = stitchwort_rt::Limits::from_core(session.elab.limits);
    let mut input = std::io::stdin().lock();
    let mut output = std::io::BufWriter::new(std::io::stdout().lock());
    let result = stitchwort_rt::run_main(&program, limits, &mut input, &mut output);
    let _ = output.flush();
    let ran = start.elapsed();
    eprintln!(
        "check {:.3}s, lower {:.3}s, run {:.3}s",
        checked.as_secs_f64(),
        (lowered - checked).as_secs_f64(),
        (ran - lowered).as_secs_f64()
    );
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("error: {e}");
            ExitCode::from(2)
        }
    }
}

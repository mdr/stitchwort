//! The codec of the lowered program (docs/proposals/standalone-executables.md,
//! stage S1): programs survive `decode(encode(p))` with the same listing,
//! the same bytecode image and the same output, and no corrupt or truncated
//! bytes make it panic.

use std::path::{Path, PathBuf};
use std::rc::Rc;

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_driver::project::{DiskFiles, Target};
use stitchwort_rt::code::{self, Image};
use stitchwort_rt::ir::{Body, Expr};
use stitchwort_rt::{Limits, Program, decode, encode, run_main};

const STACK: usize = 256 * 1024 * 1024;

fn root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn read(path: &str) -> String {
    let path = root().join(path);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()))
}

/// `source`, checked, and its `main` lowered.
fn lowered_source(file: &str, source: &str) -> (Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session.include_in_folder(
        Rc::new(DiskFiles {
            root: root().join("examples/accept"),
        }),
        file,
    );
    session
        .load(file, source)
        .unwrap_or_else(|e| panic!("{file} doesn't check: {e:?}"));
    let main = session.main().expect("a `main`");
    let program = session.lower_fast(&main).expect("lowers");
    (program, Limits::from_core(session.elab.limits))
}

fn bench(name: &str) -> (Program, Limits) {
    lowered_source(name, &read(&format!("bench/native/{name}")))
}

fn accept(name: &str) -> (Program, Limits) {
    lowered_source(name, &read(&format!("examples/accept/{name}")))
}

fn rogue() -> (Program, Limits) {
    let mut session = Session::for_stack(STACK);
    session
        .load_project(
            &DiskFiles {
                root: root().join("games/rogue"),
            },
            "rogue",
            &Target::Namespaces(vec!["Rogue".to_string()]),
        )
        .unwrap_or_else(|e| panic!("rogue doesn't check: {e:?}"));
    let main = session.main_named("Rogue.main", "rogue").expect("a `main`");
    let program = session.lower_fast(&main).expect("lowers");
    (program, Limits::from_core(session.elab.limits))
}

/// The image in a form to compare: `Image` has no `PartialEq`.
fn image_text(image: &Image) -> String {
    format!(
        "{:#?}\n{:?}\n{:?}\n{:?}\n{:#?}",
        image.codes, image.global_code, image.lambda_code, image.entry_code, image.pool
    )
}

/// What `run_main` prints with `input`, and how it ends.
fn run(program: &Program, limits: Limits, input: &str) -> (String, Result<(), String>) {
    let mut output = Vec::new();
    let result = run_main(program, limits, &mut input.as_bytes(), &mut output);
    (
        String::from_utf8_lossy(&output).into_owned(),
        result.map_err(|e| e.to_string()),
    )
}

/// The checks every round trip must pass; the decoded program is returned.
fn round_trip(program: &Program, limits: &Limits, input: &str) -> Program {
    let bytes = encode(program, limits);
    let (decoded, decoded_limits) = decode(&bytes).expect("decodes");
    assert_eq!(decoded_limits.steps, limits.steps);
    assert_eq!(decoded_limits.frames, limits.frames);
    assert_eq!(
        decoded.to_string(),
        program.to_string(),
        "the listings differ"
    );
    assert_eq!(
        encode(&decoded, &decoded_limits),
        bytes,
        "encoding the decoded program differs"
    );
    assert_eq!(
        image_text(&code::compile(&decoded)),
        image_text(&code::compile(program)),
        "the images differ"
    );
    assert_eq!(
        run(&decoded, decoded_limits, input),
        run(program, *limits, input),
        "the runs differ"
    );
    decoded
}

#[test]
fn micro_call_round_trips() {
    with_stack(STACK, || {
        let (program, limits) = bench("micro_call.sw");
        let decoded = round_trip(&program, &limits, "");
        assert_eq!(run(&decoded, limits, "").0, "20000\n");
    });
}

#[test]
fn micro_tail_round_trips() {
    with_stack(STACK, || {
        let (program, limits) = bench("micro_tail.sw");
        round_trip(&program, &limits, "");
    });
}

#[test]
fn set_nat_round_trips() {
    with_stack(STACK, || {
        let (program, limits) = bench("set_nat.sw");
        let decoded = round_trip(&program, &limits, "");
        assert_eq!(run(&decoded, limits, "").0, "1000\n");
    });
}

/// `Abort` and `IO` handled together: bind, fold and translate natives.
#[test]
fn an_effects_program_round_trips() {
    with_stack(STACK, || {
        let (program, limits) = accept("abort.sw");
        round_trip(&program, &limits, "L68 3 red\nR5 2 blue\n");
    });
}

/// The roguelike, on scripted keys. `encode`'s size is printed with
/// `--nocapture`.
#[test]
fn rogue_round_trips_and_plays_the_same() {
    with_stack(STACK, || {
        // The game seeds itself from `IO.randomSeed`: fix it, so both runs
        // play the same game.
        stitchwort_rt::host::set_random_source(|| 12345);
        let (program, limits) = rogue();
        let bytes = encode(&program, &limits);
        eprintln!("Rogue.main encodes to {} bytes", bytes.len());
        round_trip(&program, &limits, "hjklq");
    });
}

/// Bytes that don't decode: not our magic, another format version, another
/// build.
#[test]
fn foreign_bytes_are_refused() {
    with_stack(STACK, || {
        let (program, limits) = bench("micro_call.sw");
        let bytes = encode(&program, &limits);
        assert!(decode(&[]).is_err());
        assert!(decode(b"not a program").is_err());
        let mut wrong_magic = bytes.clone();
        wrong_magic[0] ^= 1;
        assert!(decode(&wrong_magic).is_err());
        let mut wrong_format = bytes.clone();
        wrong_format[4] ^= 1;
        let message = decode(&wrong_format).err().expect("refused").to_string();
        assert!(message.contains("format version"), "{message}");
        let mut wrong_version = bytes.clone();
        wrong_version[6] ^= 1; // inside the crate version's text
        assert!(decode(&wrong_version).is_err());
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(decode(&trailing).is_err());
    });
}

/// Every truncation is an error, and decoding what a flipped byte leaves
/// either fails or gives a program the image compiler accepts: never a
/// panic.
fn never_panics(bytes: &[u8], truncations: impl Iterator<Item = usize>, flips: usize) {
    for end in truncations {
        assert!(
            decode(&bytes[..end]).is_err(),
            "the first {end} bytes decoded"
        );
    }
    let stride = (bytes.len() / flips).max(1);
    for at in (0..bytes.len()).step_by(stride) {
        for mask in [0x01, 0x80, 0xff] {
            let mut flipped = bytes.to_vec();
            flipped[at] ^= mask;
            if let Ok((program, _)) = decode(&flipped) {
                let _ = code::compile(&program);
            }
        }
    }
}

#[test]
fn corrupt_and_truncated_bytes_give_errors_not_panics() {
    with_stack(STACK, || {
        let (program, limits) = bench("micro_call.sw");
        let bytes = encode(&program, &limits);
        // Every truncation and every byte flipped, for a small program.
        never_panics(&bytes, 0..bytes.len(), bytes.len());
        let (program, limits) = accept("abort.sw");
        let bytes = encode(&program, &limits);
        never_panics(&bytes, 0..bytes.len(), bytes.len());
    });
}

#[test]
fn corrupt_roguelike_bytes_give_errors_not_panics() {
    with_stack(STACK, || {
        let (program, limits) = rogue();
        let bytes = encode(&program, &limits);
        let stride = (bytes.len() / 300).max(1);
        never_panics(&bytes, (0..bytes.len()).step_by(stride), 300);
    });
}

/// A program nested far deeper than lowering makes is refused, not run out
/// of stack on.
#[test]
fn absurd_nesting_is_refused() {
    with_stack(STACK, || {
        let (mut program, limits) = bench("micro_call.sw");
        let mut expr = Expr::Unreachable;
        for _ in 0..100_000 {
            expr = Expr::If(
                Box::new(Expr::Erased),
                Box::new(Expr::Erased),
                Box::new(expr),
            );
        }
        program.entry = Body { frame: 0, expr };
        let message = decode(&encode(&program, &limits))
            .err()
            .expect("refused")
            .to_string();
        assert!(message.contains("nested too deeply"), "{message}");
        // Dropping the deep tree recurses too: keep it off the test's stack.
        std::mem::forget(program);
    });
}

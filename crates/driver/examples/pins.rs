//! Prints the pin table (`stitchwort_core::pins`): each pinned declaration,
//! the hash it is pinned to, and the hash the library's declaration has
//! now. It never writes the table: a pin is updated by hand, after checking
//! the natives that assume the declaration against its change. It then
//! lists the runtime's native bindings (`stitchwort_rt::natives`), which
//! are pinned by hash in the same way.
//!
//! cargo run --release -p stitchwort-driver --example pins   (task pins:show)

use stitchwort_core::pins;
use stitchwort_driver::driver::Session;
use stitchwort_elab::{Elaborator, prelude};
use stitchwort_rt::natives::{self, NativeBinding};
use stitchwort_syntax::SourceMap;

const STACK: usize = 64 * 1024 * 1024;

type Row = (&'static str, &'static str, Option<String>);

/// A runtime native binding: its name, its definition's hash now (if
/// loaded) and whether that is the one the native was written for.
type NativeRow = (String, Option<String>, bool);

fn table(session: &Session) -> Vec<Row> {
    pins::table(&session.elab.ev())
        .into_iter()
        .map(|(pin, now)| (pin.builtin.name(), pin.hash, now))
        .collect()
}

fn native_rows(session: &Session) -> Vec<NativeRow> {
    fn rows<N>(group: &str, bindings: &[NativeBinding<N>]) -> Vec<NativeRow> {
        (bindings.iter())
            .map(|b| (format!("{group}.{}", b.name), b.hash.clone(), b.bound))
            .collect()
    }
    let g = &session.elab.ev();
    let mut all = Vec::new();
    match natives::bind_text_natives(g) {
        Ok(b) => all.extend(rows("text", &b)),
        Err(e) => eprintln!("text natives: {e:?}"),
    }
    match natives::bind_int(g) {
        Ok(b) => {
            all.push(("int (data)".to_string(), b.hash.clone(), b.bound));
            all.extend(rows("int", &b.natives));
        }
        Err(e) => eprintln!("int natives: {e:?}"),
    }
    match natives::bind_float_natives(g) {
        Ok(b) => all.extend(rows("float", &b)),
        Err(e) => eprintln!("float natives: {e:?}"),
    }
    match natives::bind_fin_natives(g) {
        Ok(b) => all.extend(rows("fin", &b)),
        Err(e) => eprintln!("fin natives: {e:?}"),
    }
    match natives::bind_array(g) {
        Ok(b) => {
            all.push(("array (data)".to_string(), b.hash.clone(), b.bound));
            all.extend(rows("array", &b.natives));
        }
        Err(e) => eprintln!("array natives: {e:?}"),
    }
    all
}

/// Stale pins fall back, so the library loads far enough to hash them.
fn rows() -> (Vec<Row>, Vec<NativeRow>) {
    match Session::try_with_prelude_falling_back(prelude()) {
        Ok(mut session) => {
            // `Float`'s pins, and the natives of `Fin`, `Array` and some of `Text`, are in library files loaded on demand.
            let program = "import Std (Array, Fin, Float, Text)\n\
                 def zero: Float := 0.0\n\
                 def useFin (n: Nat) (i: Fin n): Nat := i.toNat\n\
                 def useArray (a: Array Nat): Nat := a.size\n\
                 def useText (t: Text): Text := t.slice 0 1\n\
                 def useGetOr (t: Text): Char := t.getOr 0 'a'\n\
                 def useGetLt (t: Text) (h: 0 < t.length): Char := t.getLt 0\n";
            if let Err(errors) = session.load("pins.sw", program) {
                eprintln!(
                    "loading the on-demand files failed ({} errors)",
                    errors.len()
                );
                for e in &errors {
                    eprintln!("  {}", e.message);
                }
            }
            (table(&session), native_rows(&session))
        }
        // A changed declaration often breaks proofs that unfold it, so the
        // core may not check at all: hash what it declares regardless.
        Err(_) => {
            eprintln!("the core doesn't check; its pins are hashed regardless\n");
            let mut session = Session {
                sources: SourceMap::new(),
                elab: Elaborator::new(),
                warnings: Vec::new(),
            };
            session.elab.options.stale_pins_fall_back = true;
            session.elab.set_loading_prelude(true);
            let _ = session.load("<prelude>", prelude());
            (table(&session), native_rows(&session))
        }
    }
}

fn main() {
    let (rows, native_rows) = std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(rows)
        .expect("a thread")
        .join()
        .expect("no panic");
    let mut stale = 0;
    for (name, pinned, now) in rows {
        let state = match now.as_deref() {
            Some(now) if now == pinned => "ok".to_string(),
            Some(now) => {
                stale += 1;
                format!("STALE, now {now}")
            }
            None => "not loaded".to_string(),
        };
        println!("{name:<20} {pinned}  {state}");
    }
    if stale > 0 {
        println!("\n{stale} stale: check each native against its declaration's change first");
    }
    println!("\nruntime native bindings (crates/rt/src/natives.rs):");
    let mut unbound = 0;
    for (name, hash, bound) in native_rows {
        let state = match (bound, hash) {
            (true, _) => "ok".to_string(),
            (false, Some(now)) => {
                unbound += 1;
                format!("CHANGED, now {now}")
            }
            (false, None) => "not loaded".to_string(),
        };
        println!("{name:<28} {state}");
    }
    if unbound > 0 {
        println!(
            "\n{unbound} native bindings no longer match: check each native, then update its hash"
        );
    }
}

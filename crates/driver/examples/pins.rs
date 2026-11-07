//! Prints the pin table (`stitchwort_core::pins`): each pinned declaration,
//! the hash it is pinned to, and the hash the library's declaration has
//! now. It never writes the table: a pin is updated by hand, after checking
//! the natives that assume the declaration against its change.
//!
//! cargo run --release -p stitchwort-driver --example pins   (task pins:show)

use stitchwort_core::pins;
use stitchwort_driver::driver::Session;
use stitchwort_elab::{Elaborator, prelude};
use stitchwort_syntax::SourceMap;

const STACK: usize = 64 * 1024 * 1024;

type Row = (&'static str, &'static str, Option<String>);

fn table(session: &Session) -> Vec<Row> {
    pins::table(&session.elab.ev())
        .into_iter()
        .map(|(pin, now)| (pin.builtin.name(), pin.hash, now))
        .collect()
}

/// Stale pins fall back, so the library loads far enough to hash them.
fn rows() -> Vec<Row> {
    match Session::try_with_prelude_falling_back(prelude()) {
        Ok(mut session) => {
            // `Float`'s pins are in a library file, loaded on demand.
            if let Err(errors) =
                session.load("pins.sw", "import Std (Float)\ndef zero: Float := 0.0\n")
            {
                eprintln!("loading `Float` failed ({} errors)", errors.len());
            }
            table(&session)
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
            table(&session)
        }
    }
}

fn main() {
    let rows = std::thread::Builder::new()
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
}

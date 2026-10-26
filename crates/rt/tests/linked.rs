//! The tables an executable built with `--native` carries (stage NO6 of
//! docs/proposals/native-only.md): they survive `decode(encode(…))` with
//! the same constant pool, number tables, operations and outline, and no
//! corrupt or truncated bytes make reading them panic.

use stitchwort_driver::driver::{Session, with_stack};
use stitchwort_rt::code::{self, Image};
use stitchwort_rt::linked::{Linked, Outline, decode, encode};
use stitchwort_rt::native_abi::{Numbering, TableStore};
use stitchwort_rt::shared::NumTable;
use stitchwort_rt::value::Value;
use stitchwort_rt::{Limits, Program};

const STACK: usize = 256 * 1024 * 1024;

/// A program with most kinds of constant the pool holds: small and big
/// numbers and integers, negative ones, texts, a float, and a number switch
/// with small and big arms. ([`with_constructors`] adds constructors.)
const SOURCE: &str = "import Std (IO, Nat, Int, Text, Float)\n\n\
    def big: Nat := 123456789012345678901234567890\n\n\
    def neg: Int := -98765432109876543210987654321\n\n\
    def small: Int := -7\n\n\
    def half: Float := 2.5\n\n\
    def classify: Nat → Text\n  \
      | 3 => \"three\"\n  \
      | 123456789012345678901234567890 => \"big\"\n  \
      | _ => \"other\"\n\n\
    def main(): {IO} () :=\n  \
      IO.print (classify big ++ classify 3 ++ Int.toText neg ++ Int.toText small ++ Nat.toText half.bits)\n";

/// `image` with constants the program has none of added to its pool (the
/// tables don't check the pool against the code): a list of a million
/// characters, as a `Chars` literal makes, deeper than any recursion could
/// read, and a constructor with no fields.
fn with_constructors(mut image: Image, program: &Program) -> Image {
    let s = &program.shapes;
    let mut list = Value::Tag(s.nil);
    for i in 0..1_000_000u64 {
        let c = Value::data(s.char_, [Value::Nat(97 + i % 26)]);
        list = Value::data(s.cons, [c, list]);
    }
    image.pool.push(list);
    image.pool.push(Value::Tag(s.unit));
    image
}

/// `a` and `b` are the same value, compared without recursion.
fn assert_same(a: &Value, b: &Value) {
    let mut pending = vec![(a, b)];
    while let Some((a, b)) = pending.pop() {
        match (a, b) {
            (Value::Data(t, xs), Value::Data(u, ys)) => {
                assert_eq!((t, xs.len()), (u, ys.len()));
                pending.extend(xs.iter().zip(ys.iter()));
            }
            (Value::Data(..), _) | (_, Value::Data(..)) => panic!("{a:?} isn't {b:?}"),
            _ => assert_eq!(format!("{a:?}"), format!("{b:?}")),
        }
    }
}

fn lowered(source: &str) -> (Program, Image, Limits) {
    let mut session = Session::for_stack(STACK);
    session
        .load("test.sw", source)
        .unwrap_or_else(|e| panic!("doesn't check: {e:?}"));
    let main = session.main().expect("a `main`");
    let program = session.lower_fast(&main).expect("lowers");
    let image = code::compile(&program);
    (program, image, Limits::from_core(session.elab.limits))
}

#[test]
fn the_tables_round_trip() {
    with_stack(STACK, || {
        let (program, image, limits) = lowered(SOURCE);
        let image = with_constructors(image, &program);
        let bytes = encode(&program, &image, &limits);
        let Linked {
            outline,
            tables,
            limits: read_limits,
        } = decode(&bytes).unwrap_or_else(|e| panic!("{e}"));
        assert_eq!(
            (read_limits.steps, read_limits.frames),
            (limits.steps, limits.frames)
        );
        assert_eq!(tables.pool.len(), image.pool.len());
        for (read, constant) in tables.pool.iter().zip(&image.pool) {
            assert_same(read, constant);
        }
        let kinds = |v: &Value| std::mem::discriminant(v);
        // (A small `Nat` is an operand, not a constant; the list has them.)
        for kind in [
            Value::BigNat(Default::default()),
            Value::Int(0),
            Value::BigInt(Default::default()),
            Value::Text("".into()),
            Value::Float(0.0),
            Value::Tag(0),
        ] {
            assert!(
                image.pool.iter().any(|v| kinds(v) == kinds(&kind)),
                "the pool has no {kind:?}"
            );
        }
        let num_tables: Vec<&NumTable> = image
            .codes
            .iter()
            .flat_map(|code| &code.num_tables)
            .collect();
        assert!(
            num_tables.iter().any(|t| !t.big.is_empty()),
            "the program has a number switch with a big arm"
        );
        assert_eq!(
            format!("{:?}", tables.num_tables),
            format!("{num_tables:?}")
        );
        assert_eq!(*tables.ops, *Numbering::of(&image).ops);
        assert_eq!(
            format!("{:?}", *tables.shapes),
            format!("{:?}", program.shapes)
        );

        let expected = Outline::of(&program, &image);
        assert_eq!(outline.main_row, expected.main_row);
        assert_eq!(
            format!("{:?}", outline.shapes),
            format!("{:?}", program.shapes)
        );
        assert_eq!(outline.lambda_params, expected.lambda_params);
        assert_eq!(outline.global_code, expected.global_code);
        assert_eq!(outline.entry_code, expected.entry_code);
        assert_eq!(outline.globals.len(), expected.globals.len());
        for (read, global) in outline.globals.iter().zip(&expected.globals) {
            assert_eq!(read.kind, global.kind);
        }
        // Names are kept for the globals the depth note can name: those
        // with a body.
        for (g, code) in expected.global_code.iter().enumerate() {
            if code.is_some() {
                assert_eq!(outline.globals[g].name, expected.globals[g].name);
            }
        }
        let deepest = [(
            image.global_code.iter().flatten().copied().next().unwrap(),
            5,
        )];
        assert_eq!(
            outline.depth_report(&deepest),
            expected.depth_report(&deepest)
        );
    });
}

#[test]
fn corrupt_and_truncated_tables_give_errors_not_panics() {
    with_stack(STACK, || {
        let (program, image, limits) = lowered(SOURCE);
        let bytes = encode(&program, &image, &limits);
        for end in 0..bytes.len() {
            assert!(decode(&bytes[..end]).is_err(), "truncated at {end}");
        }
        let mut rng = 0x2545_f491_4f6c_dd1du64;
        for _ in 0..2_000 {
            rng ^= rng << 13;
            rng ^= rng >> 7;
            rng ^= rng << 17;
            let mut corrupt = bytes.clone();
            let at = (rng as usize) % corrupt.len();
            corrupt[at] ^= (rng >> 32) as u8 | 1;
            let _ = decode(&corrupt);
        }
        let mut longer = bytes.clone();
        longer.push(0);
        assert!(decode(&longer).is_err());
        assert!(decode(b"SWRT").is_err());
    });
}

/// The tables keep their own copy of the shapes, so what later happens to
/// the `Program` they were made from doesn't reach them. `run --native`
/// moves the program after compiling it; with the tables pointing into the
/// program, it read the stale stack slot the program had left, which Linux
/// reused (a wrong `None` tag, then a trap; stage NO7 of
/// docs/proposals/native-only.md).
#[test]
fn the_tables_keep_their_own_shapes() {
    with_stack(STACK, || {
        let (mut program, image, _) = lowered(SOURCE);
        let expected = format!("{:?}", program.shapes);
        let store = TableStore::new(&program, &image, 0);
        // As if the program's old place were reused.
        program.shapes.none = u32::MAX;
        program.shapes.cons = u32::MAX;
        drop(program);
        // SAFETY: the store's tables, and what they point to, live as long
        // as the store.
        #[allow(unsafe_code)]
        let shapes = unsafe { format!("{:?}", *(*store.tables()).shapes) };
        assert_eq!(shapes, expected);
    });
}

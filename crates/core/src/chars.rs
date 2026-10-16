//! Compact text (docs/proposals/compact-text.md, option B1).
//!
//! `Text` is `MkText (chars : List Char)` in the prelude, and that's what it
//! means. But the characters of a text literal are *stored* as one range of
//! an array, [`Chars`]: `Term::Chars` and `Value::Chars`. Its meaning is its
//! *expansion*, built only from constructors:
//!
//! ```text
//! expand(Chars [c₀, …, cₙ₋₁]) = Cons (MkChar c₀ rfl) (Cons … (Cons (MkChar cₙ₋₁ rfl) Nil))
//! ```
//!
//! and every operation must commute with it: matching a range takes the
//! branch, and binds the fields, that matching its expansion would
//! ([`step`]); conversion and unification compare a range with anything but
//! another range by expanding it one cell at a time; quotation gives a range
//! back, which means the same. So a range is a closed inhabitant of an
//! existing type, with no new reduction or recursion principle: no list
//! is ever *made* compact by evaluation, only literals are.
//!
//! The expansion claims `rfl : isScalar c = True` for every character, which
//! is only true because a Rust `char` is a scalar value and because `isScalar`
//! is the prelude's definition. So the representation is bound to the exact
//! declarations of `List` and `Char` by content hash (which covers `Nil`,
//! `Cons`, `MkChar`, `isScalar` and everything `isScalar` uses): see
//! [`register`]. If they differ, text literals are elaborated as constructors,
//! as before, and the kernel refuses a `Term::Chars`.
//!
//! These rules are part of the trusted base (DESIGN.md §13).

use std::rc::Rc;

use num_bigint::BigUint;

use crate::budget::Limits;
use crate::globals::{Globals, State};
use crate::hash::data_hash;
use crate::term::{DataId, Sort, Term};
use crate::value::Value;

/// The characters `buf[start..end]`, standing for the list of `MkChar c rfl`
/// for each. Equal ranges of different buffers mean the same list, so
/// nothing (hashing, conversion) looks at the buffer or the offsets, only at
/// [`Chars::as_slice`].
#[derive(Clone)]
pub struct Chars {
    buf: Rc<[char]>,
    start: usize,
    end: usize,
}

impl Chars {
    /// The range `buf[start..end]`, if those are its bounds. The only way to
    /// make one, so every range is within its buffer.
    pub fn new(buf: Rc<[char]>, start: usize, end: usize) -> Option<Chars> {
        (start <= end && end <= buf.len()).then_some(Chars { buf, start, end })
    }

    /// All of `buf`.
    pub fn whole(buf: Rc<[char]>) -> Chars {
        let end = buf.len();
        Chars { buf, start: 0, end }
    }

    pub fn as_slice(&self) -> &[char] {
        &self.buf[self.start..self.end]
    }

    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// The first character and the range after it, or `None` if it's empty.
    pub fn uncons(&self) -> Option<(char, Chars)> {
        let first = *self.as_slice().first()?;
        let rest = Chars {
            buf: self.buf.clone(),
            start: self.start + 1,
            end: self.end,
        };
        Some((first, rest))
    }

    /// The same characters, in a buffer of their own if this range is less
    /// than half of its buffer, so a short range doesn't keep a long buffer
    /// alive. Copying costs at most the range's length. For ranges that are
    /// kept: quoted into terms.
    pub fn compacted(&self) -> Chars {
        if self.len() * 2 >= self.buf.len() {
            return self.clone();
        }
        Chars::whole(self.as_slice().into())
    }

    /// The buffer this range shares, for tests of memory retention.
    pub fn buffer(&self) -> &Rc<[char]> {
        &self.buf
    }
}

impl std::fmt::Debug for Chars {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let text: String = self.as_slice().iter().collect();
        write!(f, "Chars({text:?})")
    }
}

/// The declarations a compact list stands for, once [`register`]ed: `List`
/// (constructor 0 is `Nil`, 1 is `Cons`) and `Char` (constructor 0 is
/// `MkChar code valid`).
#[derive(Clone, Debug)]
pub struct CompactText {
    pub list: DataId,
    pub char: DataId,
    /// `MkChar c rfl` for the first [`SHARED`] code points, made once and
    /// shared by every match on a compact list, as a literal's constructors
    /// would share them. Others are made as they're matched.
    small: Rc<[Value]>,
}

/// How many characters' values are made once (see [`CompactText`]): Latin-1.
const SHARED: u32 = 256;

impl CompactText {
    pub fn new(list: DataId, char: DataId) -> CompactText {
        let small = (0..SHARED)
            .filter_map(char::from_u32)
            .map(|c| new_char_value(char, c))
            .collect();
        CompactText { list, char, small }
    }
}

/// The content hashes (DESIGN.md §11) of the prelude's `List` and `Char`,
/// which the compact representation was written for. `Char`'s covers
/// `MkChar`'s field types, and so `isScalar` and everything it uses.
const LIST_HASH: &str = "478989f1d859e17f3b556d5d4a33a9ca52e5587e6979f7703753f6462df3c094";
const CHAR_HASH: &str = "cf82b6a2de144a6218c3efd371dd1513e5b30e458cce6ba7f631b827f038aaac";

/// Whether `List` and `Char` are the declarations the compact representation
/// was written for, and their hashes: for the test that fails when the
/// prelude changes them, which prints the new ones.
pub struct Binding {
    pub list_hash: Option<String>,
    pub char_hash: Option<String>,
    pub bound: bool,
}

/// Compares `list` and `char` with the declarations the compact
/// representation was written for, by content hash.
pub fn binding(g: &Globals, list: DataId, char: DataId) -> Binding {
    // Hashing a reference hashes what it refers to first, which needs an
    // operation for its depth guard.
    let _op = g
        .budget
        .operation(Limits::stack_only(Limits::default().stack));
    let hex = |d| data_hash(g, d).ok().flatten().map(|h| h.hex());
    let (list_hash, char_hash) = (hex(list), hex(char));
    let bound = list_hash.as_deref() == Some(LIST_HASH) && char_hash.as_deref() == Some(CHAR_HASH);
    Binding {
        list_hash,
        char_hash,
        bound,
    }
}

/// Registers the compact representation for `List` and `Char`, while the
/// prelude loads, if they're exactly the declarations it was written for
/// (by content hash); otherwise it stays unregistered, and text literals
/// are constructors. Returns whether it was registered.
///
/// The hash fixes their shape too; the shape is checked anyway, as the rules
/// rely on it: `List` has one parameter, `Nil` and then `Cons` with two
/// fields; `Char` has none, and `MkChar` has two fields.
pub fn register(g: &mut Globals, list: DataId, char: DataId) -> bool {
    let shaped = |d: DataId, params: usize, fields: &[usize]| {
        let data = g.data(d);
        data.state == State::Final
            && data.params.len() == params
            && data.sort == Sort::Type(0)
            && data
                .ctors
                .iter()
                .map(|c| c.fields.len())
                .eq(fields.iter().copied())
    };
    if !(shaped(list, 1, &[0, 2]) && shaped(char, 0, &[2]) && binding(g, list, char).bound) {
        return false;
    }
    g.builtins.text = Some(CompactText::new(list, char));
    true
}

/// A compact list's value: `Nil` if it's empty (which keeps no buffer
/// alive), and otherwise the range.
pub fn value(text: &CompactText, chars: Chars) -> Value {
    if chars.is_empty() {
        Value::Ctor(text.list, 0, [].into())
    } else {
        Value::Chars(chars)
    }
}

/// One step of the expansion: what matching on the range finds. `Nil` for an
/// empty range, otherwise `Cons (MkChar c rfl) rest`, with `rest` the range
/// after `c`, sharing the buffer.
pub fn step(text: &CompactText, chars: &Chars) -> Value {
    let (c, fields) = split(text, chars);
    Value::Ctor(text.list, c, fields.into())
}

/// [`step`], as the constructor and its fields: what a `case` binds.
pub fn split(text: &CompactText, chars: &Chars) -> (usize, Vec<Value>) {
    match chars.uncons() {
        None => (0, Vec::new()),
        Some((c, rest)) => (1, vec![char_value(text, c), value(text, rest)]),
    }
}

/// `MkChar c rfl`.
pub fn char_value(text: &CompactText, c: char) -> Value {
    match text.small.get(u32::from(c) as usize) {
        Some(shared) => shared.clone(),
        None => new_char_value(text.char, c),
    }
}

fn new_char_value(char: DataId, c: char) -> Value {
    let code = Value::Nat(Rc::new(BigUint::from(u32::from(c))));
    Value::Ctor(char, 0, [code, Value::Refl].into())
}

/// A compact list's term: `Nil` if it's empty, and otherwise the range,
/// copied into its own buffer if it's short (see [`Chars::compacted`]).
pub fn term(text: &CompactText, chars: &Chars) -> Term {
    if chars.is_empty() {
        Term::Ctor(text.list, 0, Vec::new())
    } else {
        Term::Chars(chars.compacted())
    }
}

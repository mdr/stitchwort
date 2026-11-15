//! A text at run time (docs/proposals/file-io-and-text.md §4.2).
//!
//! A [`Text`] is a reference to a shared buffer of characters and the start
//! and length of its part of that buffer, both counted in characters
//! (Unicode scalar values), which are the positions `Text.toList` numbers.
//! So finding a character by position, cutting a piece out (`take`, `drop`,
//! `slice`, `uncons`) and asking the length are arithmetic on two numbers:
//! constant time, and a piece shares its buffer rather than copying it.
//!
//! A buffer stores every character at one width, the narrowest that holds
//! its largest ([`Units`]; Python's layout, PEP 393). One-byte buffers hold
//! only ASCII, so their bytes are also their UTF-8, and printing, searching
//! and comparing them is the same as on a `str`. Every buffer is made at its
//! narrowest width; a piece keeps its buffer's, so two equal texts may be
//! stored at different widths, and equality and order compare characters,
//! never units.
//!
//! **Pieces keep their buffer alive.** A short piece of a long buffer is
//! copied instead ([`COPY_AT_MOST`], [`COPY_FROM`]), so that a token kept
//! from a large file doesn't hold the whole file; the copy is at most
//! [`COPY_AT_MOST`] characters, so cutting stays constant time.

use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::rc::Rc;

/// A buffer's characters, at one width.
#[derive(Debug)]
pub enum Units {
    /// Every character is below U+0080: a byte each, which is also UTF-8.
    Ascii(String),
    /// Every character is below U+10000 (so none is a surrogate): two bytes
    /// each, the character's scalar value.
    Bmp(Vec<u16>),
    /// Any characters: four bytes each.
    Full(Vec<char>),
}

impl Units {
    fn len(&self) -> usize {
        match self {
            Units::Ascii(s) => s.len(),
            Units::Bmp(v) => v.len(),
            Units::Full(v) => v.len(),
        }
    }

    fn width(&self) -> Width {
        match self {
            Units::Ascii(_) => Width::Ascii,
            Units::Bmp(_) => Width::Bmp,
            Units::Full(_) => Width::Full,
        }
    }
}

/// The widths a buffer can have, narrowest first.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Width {
    Ascii,
    Bmp,
    Full,
}

impl Width {
    fn of(c: char) -> Width {
        match u32::from(c) {
            0..0x80 => Width::Ascii,
            0x80..0x1_0000 => Width::Bmp,
            _ => Width::Full,
        }
    }

    /// The narrowest width that holds every one of `chars`.
    fn of_all(chars: impl Iterator<Item = char>) -> Width {
        let mut width = Width::Ascii;
        for c in chars {
            width = width.max(Width::of(c));
            if width == Width::Full {
                break;
            }
        }
        width
    }
}

/// A piece of at most this many characters, of a buffer of at least
/// [`COPY_FROM`], is copied rather than shared.
pub const COPY_AT_MOST: usize = 32;
/// See [`COPY_AT_MOST`].
pub const COPY_FROM: usize = 1024;

/// A text: its buffer, and where its characters are in it.
///
/// `repr(C)`, so that the buffer's `Rc` is a `Value::Text`'s word at byte 8,
/// as every owning value's is, and the start and length follow it at bytes
/// 16 and 20 (`crate::native_abi::probe_layout` checks this). Native code
/// copies and counts a text's references and never looks inside it.
#[derive(Clone)]
#[repr(C)]
pub struct Text {
    units: Rc<Units>,
    start: u32,
    len: u32,
}

thread_local! {
    /// The empty text's buffer, shared, so that an empty result never
    /// allocates.
    static EMPTY: Rc<Units> = Rc::new(Units::Ascii(String::new()));
}

impl Text {
    /// The whole of a new buffer.
    fn whole(units: Units) -> Text {
        let len = units.len();
        let Ok(len) = u32::try_from(len) else {
            panic!(
                "internal error: a text of {len} characters, more than a text can hold (2^32 - 1)"
            )
        };
        Text {
            units: Rc::new(units),
            start: 0,
            len,
        }
    }

    pub fn empty() -> Text {
        Text {
            units: EMPTY.with(Rc::clone),
            start: 0,
            len: 0,
        }
    }

    /// The text of these characters, at the narrowest width.
    pub fn from_chars(chars: &[char]) -> Text {
        if chars.is_empty() {
            return Text::empty();
        }
        Text::whole(units_of(
            Width::of_all(chars.iter().copied()),
            chars.len(),
            chars.iter().copied(),
        ))
    }

    /// How many characters it has.
    #[inline]
    pub fn len(&self) -> usize {
        self.len as usize
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// The character at `index`, if it has that many.
    #[inline]
    pub fn get(&self, index: usize) -> Option<char> {
        if index >= self.len() {
            return None;
        }
        let at = self.start as usize + index;
        Some(match &*self.units {
            Units::Ascii(s) => char::from(s.as_bytes()[at]),
            Units::Bmp(v) => bmp_char(v[at]),
            Units::Full(v) => v[at],
        })
    }

    /// The characters from `from` up to (not including) `to`, which must be
    /// in order and within the text.
    pub fn slice(&self, from: usize, to: usize) -> Text {
        assert!(
            from <= to && to <= self.len(),
            "internal error: the piece {from}..{to} of a text of {} characters",
            self.len()
        );
        if from == 0 && to == self.len() {
            return self.clone();
        }
        let len = to - from;
        if len == 0 {
            return Text::empty();
        }
        if len <= COPY_AT_MOST && self.units.len() >= COPY_FROM {
            let piece = Text {
                units: Rc::clone(&self.units),
                start: self.start + from as u32,
                len: len as u32,
            };
            let width = Width::of_all(piece.chars());
            return Text::whole(units_of(width, len, piece.chars()));
        }
        Text {
            units: Rc::clone(&self.units),
            start: self.start + from as u32,
            len: len as u32,
        }
    }

    /// The characters after the first `n` (all of them past the end).
    pub fn skip(&self, n: usize) -> Text {
        self.slice(n.min(self.len()), self.len())
    }

    /// The first `n` characters (all of them past the end).
    pub fn prefix(&self, n: usize) -> Text {
        self.slice(0, n.min(self.len()))
    }

    /// Its characters, in order.
    pub fn chars(&self) -> Chars<'_> {
        let (from, to) = (self.start as usize, self.start as usize + self.len());
        match &*self.units {
            Units::Ascii(s) => Chars::Ascii(s.as_bytes()[from..to].iter()),
            Units::Bmp(v) => Chars::Bmp(v[from..to].iter()),
            Units::Full(v) => Chars::Full(v[from..to].iter()),
        }
    }

    /// The text as a `str`, if its buffer is ASCII: borrowed, so free.
    #[inline]
    pub fn ascii(&self) -> Option<&str> {
        match &*self.units {
            Units::Ascii(s) => Some(&s[self.start as usize..self.start as usize + self.len()]),
            _ => None,
        }
    }

    /// The text as a `str`: borrowed if its buffer is ASCII, otherwise
    /// encoded as UTF-8.
    pub fn to_str(&self) -> Cow<'_, str> {
        match self.ascii() {
            Some(s) => Cow::Borrowed(s),
            None => Cow::Owned(self.chars().collect()),
        }
    }

    /// How many bytes its UTF-8 takes.
    pub fn utf8_len(&self) -> usize {
        match self.ascii() {
            Some(s) => s.len(),
            None => self.chars().map(char::len_utf8).sum(),
        }
    }

    /// The bytes a buffer of its characters takes, for the value census.
    pub fn buffer_bytes(&self) -> usize {
        self.len()
            * match self.units.width() {
                Width::Ascii => 1,
                Width::Bmp => 2,
                Width::Full => 4,
            }
    }

    /// Where its buffer is, for the check of the layout native code reads.
    pub(crate) fn units_address(&self) -> *const u8 {
        Rc::as_ptr(&self.units).cast()
    }

    /// How many texts share its buffer (for the machine's own checks).
    pub fn references(&self) -> usize {
        Rc::strong_count(&self.units)
    }

    /// The narrowest width that holds its characters: its buffer's, unless
    /// that is wider than a piece of it needs.
    fn width(&self) -> Width {
        match self.units.width() {
            Width::Ascii => Width::Ascii,
            _ => Width::of_all(self.chars()),
        }
    }

    /// The texts one after another, with `separator` between each two: one
    /// new buffer, at the narrowest width (an empty or single text is
    /// returned as it is).
    pub fn join<'a>(
        texts: impl Iterator<Item = &'a Text> + Clone,
        separator: Option<char>,
    ) -> Text {
        let mut count = 0usize;
        let mut len = 0usize;
        let mut width = separator.map_or(Width::Ascii, Width::of);
        let mut only = None;
        for t in texts.clone() {
            count += 1;
            len += t.len();
            if t.units.width() > width {
                width = width.max(t.width());
            }
            only = Some(t);
        }
        let separators = if separator.is_some() {
            count.saturating_sub(1)
        } else {
            0
        };
        if separators == 0 {
            match only {
                None => return Text::empty(),
                Some(t) if count == 1 => return t.clone(),
                _ if len == 0 => return Text::empty(),
                _ => {}
            }
        }
        let len = len + separators;
        let mut first = true;
        let chars = texts.flat_map(move |t| {
            let sep = if first { None } else { separator };
            first = false;
            sep.into_iter().chain(t.chars())
        });
        Text::whole(units_of(width, len, chars))
    }

    /// The text `n` times over, in one new buffer of its width.
    pub fn repeat(&self, n: usize) -> Text {
        if self.is_empty() || n == 0 {
            return Text::empty();
        }
        if n == 1 {
            return self.clone();
        }
        let len = self.len().saturating_mul(n);
        let width = self.width();
        Text::whole(units_of(width, len, (0..n).flat_map(|_| self.chars())))
    }
}

impl From<&str> for Text {
    fn from(s: &str) -> Text {
        if s.is_ascii() {
            return Text::from(s.to_string());
        }
        let width = Width::of_all(s.chars());
        Text::whole(units_of(width, s.chars().count(), s.chars()))
    }
}

impl From<String> for Text {
    /// An ASCII string becomes the buffer itself, with no copy.
    fn from(s: String) -> Text {
        if s.is_empty() {
            Text::empty()
        } else if s.is_ascii() {
            Text::whole(Units::Ascii(s))
        } else {
            Text::from(&*s)
        }
    }
}

/// A buffer of `len` characters at `width`, which holds every one of them.
fn units_of(width: Width, len: usize, chars: impl Iterator<Item = char>) -> Units {
    match width {
        Width::Ascii => {
            let mut s = String::with_capacity(len);
            s.extend(chars);
            debug_assert!(s.is_ascii());
            Units::Ascii(s)
        }
        Width::Bmp => {
            let mut v = Vec::with_capacity(len);
            v.extend(chars.map(|c| {
                debug_assert!(Width::of(c) <= Width::Bmp);
                u32::from(c) as u16
            }));
            Units::Bmp(v)
        }
        Width::Full => {
            let mut v = Vec::with_capacity(len);
            v.extend(chars);
            Units::Full(v)
        }
    }
}

/// A two-byte unit's character: never a surrogate, since it was made from
/// one.
#[inline]
fn bmp_char(unit: u16) -> char {
    char::from_u32(u32::from(unit)).expect("a two-byte unit is a character")
}

/// A text's characters, in either direction.
pub enum Chars<'a> {
    Ascii(std::slice::Iter<'a, u8>),
    Bmp(std::slice::Iter<'a, u16>),
    Full(std::slice::Iter<'a, char>),
}

impl Iterator for Chars<'_> {
    type Item = char;

    #[inline]
    fn next(&mut self) -> Option<char> {
        match self {
            Chars::Ascii(it) => it.next().map(|&b| char::from(b)),
            Chars::Bmp(it) => it.next().map(|&u| bmp_char(u)),
            Chars::Full(it) => it.next().copied(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let n = self.len();
        (n, Some(n))
    }
}

impl DoubleEndedIterator for Chars<'_> {
    #[inline]
    fn next_back(&mut self) -> Option<char> {
        match self {
            Chars::Ascii(it) => it.next_back().map(|&b| char::from(b)),
            Chars::Bmp(it) => it.next_back().map(|&u| bmp_char(u)),
            Chars::Full(it) => it.next_back().copied(),
        }
    }
}

impl ExactSizeIterator for Chars<'_> {
    fn len(&self) -> usize {
        match self {
            Chars::Ascii(it) => it.len(),
            Chars::Bmp(it) => it.len(),
            Chars::Full(it) => it.len(),
        }
    }
}

/// The units of a piece of a buffer, for comparing two pieces of the same
/// width as slices.
enum Piece<'a> {
    Ascii(&'a [u8]),
    Bmp(&'a [u16]),
    Full(&'a [char]),
}

impl Text {
    fn piece(&self) -> Piece<'_> {
        let (from, to) = (self.start as usize, self.start as usize + self.len());
        match &*self.units {
            Units::Ascii(s) => Piece::Ascii(&s.as_bytes()[from..to]),
            Units::Bmp(v) => Piece::Bmp(&v[from..to]),
            Units::Full(v) => Piece::Full(&v[from..to]),
        }
    }
}

impl PartialEq for Text {
    fn eq(&self, other: &Text) -> bool {
        if self.len != other.len {
            return false;
        }
        if Rc::ptr_eq(&self.units, &other.units) && self.start == other.start {
            return true;
        }
        match (self.piece(), other.piece()) {
            (Piece::Ascii(a), Piece::Ascii(b)) => a == b,
            (Piece::Bmp(a), Piece::Bmp(b)) => a == b,
            (Piece::Full(a), Piece::Full(b)) => a == b,
            _ => self.chars().eq(other.chars()),
        }
    }
}

impl Eq for Text {}

impl Ord for Text {
    /// Lexicographically by scalar value: each width's units are scalar
    /// values, so a slice comparison is the same order.
    fn cmp(&self, other: &Text) -> Ordering {
        match (self.piece(), other.piece()) {
            (Piece::Ascii(a), Piece::Ascii(b)) => a.cmp(b),
            (Piece::Bmp(a), Piece::Bmp(b)) => a.cmp(b),
            (Piece::Full(a), Piece::Full(b)) => a.cmp(b),
            _ => self.chars().cmp(other.chars()),
        }
    }
}

impl PartialOrd for Text {
    fn partial_cmp(&self, other: &Text) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Debug for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.to_str(), f)
    }
}

impl fmt::Display for Text {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// One character from each width, a combining accent, the characters
    /// either side of the surrogates, and the last.
    const ALPHABET: [char; 7] = [
        'a',
        '\u{E9}',
        '\u{301}',
        '\u{2192}',
        '\u{D7FF}',
        '\u{E000}',
        '\u{10FFFF}',
    ];

    /// Every text of up to three characters over [`ALPHABET`].
    fn small_texts() -> Vec<Vec<char>> {
        let mut out = vec![vec![]];
        let mut last = vec![vec![]];
        for _ in 0..3 {
            let mut next = Vec::new();
            for t in &last {
                for &c in &ALPHABET {
                    let mut t = t.clone();
                    t.push(c);
                    next.push(t);
                }
            }
            out.extend(next.iter().cloned());
            last = next;
        }
        out
    }

    /// The same characters stored three ways: in their own buffer, and as a
    /// piece of a two-byte and of a four-byte buffer.
    fn stored(chars: &[char]) -> Vec<Text> {
        let mut out = vec![Text::from_chars(chars)];
        for wide in ['\u{2192}', '\u{1F600}'] {
            let mut all = vec![wide];
            all.extend_from_slice(chars);
            all.push(wide);
            out.push(Text::from_chars(&all).slice(1, 1 + chars.len()));
        }
        out
    }

    /// Tier 1 (§4.4): every operation, on every small text stored every
    /// way, at every pair of positions, agrees with the list of characters.
    #[test]
    fn small_texts_agree_with_their_characters() {
        let texts = small_texts();
        for chars in &texts {
            let s: String = chars.iter().collect();
            for t in stored(chars) {
                assert_eq!(t.len(), chars.len());
                assert_eq!(t.chars().collect::<Vec<_>>(), *chars);
                assert_eq!(t.chars().rev().collect::<Vec<_>>(), {
                    let mut r = chars.clone();
                    r.reverse();
                    r
                });
                assert_eq!(t.to_str(), s);
                assert_eq!(t.utf8_len(), s.len());
                for i in 0..=chars.len() + 1 {
                    assert_eq!(t.get(i), chars.get(i).copied());
                    assert_eq!(
                        t.skip(i).chars().collect::<Vec<_>>(),
                        chars[i.min(chars.len())..]
                    );
                    assert_eq!(
                        t.prefix(i).chars().collect::<Vec<_>>(),
                        chars[..i.min(chars.len())]
                    );
                    for j in i..=chars.len() {
                        let piece = t.slice(i.min(j), j);
                        assert_eq!(piece.chars().collect::<Vec<_>>(), chars[i.min(j)..j]);
                        // A piece of a piece.
                        for k in 0..=piece.len() {
                            assert_eq!(
                                piece.skip(k).chars().collect::<Vec<_>>(),
                                chars[i.min(j) + k..j]
                            );
                        }
                    }
                }
                assert_eq!(t.repeat(2).chars().count(), 2 * chars.len());
            }
        }
    }

    /// Equality and order across widths are by character.
    #[test]
    fn equality_and_order_compare_characters_across_widths() {
        let texts: Vec<Vec<char>> = small_texts().into_iter().filter(|t| t.len() <= 2).collect();
        for a in &texts {
            for b in &texts {
                let expected = a.cmp(b);
                for x in stored(a) {
                    for y in stored(b) {
                        assert_eq!(x.cmp(&y), expected, "{a:?} {b:?}");
                        assert_eq!(x == y, expected == Ordering::Equal, "{a:?} {b:?}");
                    }
                }
            }
        }
    }

    /// Joining crosses widths: an ASCII buffer meeting `→` or an astral
    /// character is widened, and a wide buffer's ASCII piece is narrowed.
    #[test]
    fn joins_take_the_narrowest_width_that_holds_them() {
        let ascii = Text::from("ab");
        let arrow = Text::from("\u{2192}");
        let astral = Text::from("\u{1F600}");
        let joined = Text::join([&ascii, &arrow].into_iter(), None);
        assert_eq!(joined.to_str(), "ab\u{2192}");
        assert_eq!(joined.units.width(), Width::Bmp);
        let joined = Text::join([&ascii, &astral, &arrow].into_iter(), Some(','));
        assert_eq!(joined.to_str(), "ab,\u{1F600},\u{2192}");
        assert_eq!(joined.units.width(), Width::Full);
        let narrow = Text::from("\u{2192}xy\u{2192}").slice(1, 3);
        let joined = Text::join([&narrow, &ascii].into_iter(), None);
        assert_eq!(joined.to_str(), "xyab");
        assert_eq!(joined.units.width(), Width::Ascii);
        assert_eq!(Text::join(std::iter::empty(), Some(',')).len(), 0);
        let one = Text::join([&arrow].into_iter(), Some(','));
        assert!(Rc::ptr_eq(&one.units, &arrow.units));
    }

    /// A long piece shares its buffer; a short piece of a long buffer is a
    /// copy at its own narrowest width.
    #[test]
    fn short_pieces_of_long_buffers_are_copied() {
        let long = Text::from(format!("\u{2192}{}", "a".repeat(COPY_FROM)).as_str());
        let shared = long.slice(1, 1 + COPY_AT_MOST + 1);
        assert!(Rc::ptr_eq(&shared.units, &long.units));
        let copied = long.slice(1, 1 + COPY_AT_MOST);
        assert!(!Rc::ptr_eq(&copied.units, &long.units));
        assert_eq!(copied.units.width(), Width::Ascii);
        assert_eq!(copied.to_str(), "a".repeat(COPY_AT_MOST));
        let small = Text::from("\u{2192}abc");
        assert!(Rc::ptr_eq(&small.slice(1, 2).units, &small.units));
    }
}

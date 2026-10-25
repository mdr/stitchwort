-- `Key`: the keys a terminal program reads, and `Key.next`, which decodes
-- them from the bytes a terminal sends (docs/proposals/terminal-io.md §3.2).
-- Decoding is ordinary code: total, structural, with no `IO`, so it's
-- tested here and proved about (`Key.nextBytes`). `Terminal.readKey` gives
-- these keys; `Terminal.toIO` reads the bytes and calls `Key.next`.
--
--   Key.next [27, 91, 65, 113] = Got Up [113]   -- ESC [ A is the up arrow
--   Key.next [27] = Incomplete                  -- a lone ESC, or the start of a sequence?
--   Key.next [] = NoBytes

import Key.Decoded (Got, Incomplete, NoBytes)

-- A key. Arrows and the other named keys are what a terminal sends for
-- them; anything it sends that isn't one of these is `Unknown` (D1259), so
-- a program's catch-all case skips it. Not here: function keys, Alt, and
-- modified arrows (Ctrl-Up arrives as `Unknown`).
type Key: Type =
  | Printable (char: Char) -- a printable character, space included
  | Enter
  | Tab
  | Backspace
  | Escape
  | Delete
  | Up
  | Down
  | Left
  | Right
  | Home
  | End
  | PageUp
  | PageDown
  | Ctrl (letter: Char) -- Ctrl with a letter: `Ctrl 'a'`, and so on
  | Unknown -- bytes that aren't one of the above

-- `==` on keys, written by hand (the library's types get no derived one):
-- a key is its constructor's position and its character, if it has one.

def Key.position: Key → Nat
  | Printable char => 0
  | Enter => 1
  | Tab => 2
  | Backspace => 3
  | Escape => 4
  | Delete => 5
  | Up => 6
  | Down => 7
  | Left => 8
  | Right => 9
  | Home => 10
  | End => 11
  | PageUp => 12
  | PageDown => 13
  | Ctrl letter => 14
  | Unknown => 15

-- The key's character, or a space for a key without one.
def Key.charOrSpace: Key → Char
  | Printable char => char
  | Ctrl letter => letter
  | _ => ' '

-- The key at a position, with a character if it takes one: undoes
-- `position` and `charOrSpace` together (`Key.fromParts`).
def Key.ofParts (position: Nat) (char: Char): Key :=
  match position with
    | 0 => Printable char
    | 1 => Enter
    | 2 => Tab
    | 3 => Backspace
    | 4 => Escape
    | 5 => Delete
    | 6 => Up
    | 7 => Down
    | 8 => Left
    | 9 => Right
    | 10 => Home
    | 11 => End
    | 12 => PageUp
    | 13 => PageDown
    | 14 => Ctrl char
    | _ => Unknown

theorem Key.fromParts: (key: Key) → Key.ofParts (Key.position key) (Key.charOrSpace key) = key
  | Printable char => rfl
  | Enter => rfl
  | Tab => rfl
  | Backspace => rfl
  | Escape => rfl
  | Delete => rfl
  | Up => rfl
  | Down => rfl
  | Left => rfl
  | Right => rfl
  | Home => rfl
  | End => rfl
  | PageUp => rfl
  | PageDown => rfl
  | Ctrl letter => rfl
  | Unknown => rfl

theorem Key.ofPartsCong (p: Nat) (q: Nat) (c: Char) (d: Char) (samePosition: p = q) (sameChar: c = d): Key.ofParts p c = Key.ofParts q d :=
  rewrite samePosition, sameChar in rfl

theorem Key.partsInjective (a: Key) (b: Key) (samePosition: Key.position a = Key.position b) (sameChar: Key.charOrSpace a = Key.charOrSpace b): a = b :=
  Eq.trans (Eq.sym (Key.fromParts a))
    (Eq.trans (Key.ofPartsCong (Key.position a) (Key.position b) (Key.charOrSpace a) (Key.charOrSpace b) samePosition sameChar) (Key.fromParts b))

instance Key.instDecEq: DecEq Key :=
  { decide = a b =>
    if samePosition: Key.position a = Key.position b then
      if sameChar: Key.charOrSpace a = Key.charOrSpace b then Yes (Key.partsInjective a b samePosition sameChar)
      else No (e => sameChar (Eq.cong Key.charOrSpace e))
    else No (e => samePosition (Eq.cong Key.position e)) }

-- What decoding the front of some bytes gives.
type Key.Decoded: Type =
  | Got (key: Key) (rest: List Nat) -- a key, and the bytes after it
  | Incomplete -- the bytes end inside a key's sequence: more may complete it
  | NoBytes -- no bytes at all

-- The first key in `bytes`. Bytes are below 256 (larger numbers are
-- `Unknown`).
--
-- - CR or LF is `Enter`; 9 is `Tab`; 127 or 8 is `Backspace`; other bytes
--   from 1 to 26 are `Ctrl` with a letter (1 is `Ctrl 'a'`); 0 and 28 to 31
--   are `Unknown`.
-- - A character of one to four bytes of UTF-8 is `Printable`. A bad lead or
--   continuation byte, an overlong form, or a code that isn't a scalar value
--   is `Unknown`.
-- - `ESC [`, parameter bytes and a final byte is a CSI sequence: the arrows,
--   `Home`, `End`, `Delete`, `PageUp` and `PageDown` as terminals send them,
--   any other complete one `Unknown`. `ESC O` and one byte is the SS3 form
--   of the arrows, `Home` and `End`.
-- - `ESC` followed by anything else is `Escape`; the byte after it is the
--   start of the next key.
def Key.next: List Nat → Key.Decoded
  | [] => NoBytes
  | [byte, ..rest] =>
    if byte == 27 then Key.afterEscape rest
    else if byte < 128 then Got (Key.ofAscii byte) rest
    else Key.utf8Lead byte rest

-- A byte below 128 other than ESC: a control key or a printable character.
def Key.ofAscii (byte: Nat): Key :=
  if 32 ≤ byte && byte ≤ 126 then Option.fold (Char.fromNat byte) Unknown Printable
  else if byte == 13 || byte == 10 then Enter
  else if byte == 9 then Tab
  else if byte == 127 || byte == 8 then Backspace
  else if 1 ≤ byte && byte ≤ 26 then Option.fold (Char.fromNat (byte + 96)) Unknown Ctrl
  else Unknown

-- The bytes after an `ESC`.
def Key.afterEscape: List Nat → Key.Decoded
  | [] => Incomplete
  | [byte, ..rest] =>
    if byte == 91 then Key.csi [] rest
    else if byte == 79 then Key.ss3 rest
    else Got Escape (Cons byte rest)

-- After `ESC [`: parameter and intermediate bytes (32 to 63), collected in
-- reverse, then a final byte (64 to 126). Any other byte ends the sequence
-- as `Unknown`, and starts the next key.
def Key.csi (parameters: List Nat): List Nat → Key.Decoded
  | [] => Incomplete
  | [byte, ..rest] =>
    if 32 ≤ byte && byte ≤ 63 then Key.csi (Cons byte parameters) rest
    else if 64 ≤ byte && byte ≤ 126 then Got (Key.ofCsi (List.reverse parameters) byte) rest
    else Got Unknown (Cons byte rest)

-- The key a CSI sequence stands for, from its parameter bytes and final
-- byte: `ESC [A` to `ESC [D` the arrows, `ESC [H` and `ESC [F` `Home` and
-- `End`, and `ESC [n~` for the keys above the arrows.
def Key.ofCsi (parameters: List Nat) (final: Nat): Key :=
  match parameters with
    | [] => Key.ofFinal final
    | [parameter] => if final == 126 then Key.ofTilde parameter else Unknown
    | _ => Unknown

-- The final byte of `ESC [x` or `ESC Ox`.
def Key.ofFinal (final: Nat): Key :=
  if final == 65 then Up
  else if final == 66 then Down
  else if final == 67 then Right
  else if final == 68 then Left
  else if final == 72 then Home
  else if final == 70 then End
  else Unknown

-- The digit of `ESC [n~`: 3 `Delete`, 5 and 6 `PageUp` and `PageDown`, 1
-- and 7 `Home`, 4 and 8 `End`.
def Key.ofTilde (digit: Nat): Key :=
  if digit == 51 then Delete
  else if digit == 53 then PageUp
  else if digit == 54 then PageDown
  else if digit == 49 || digit == 55 then Home
  else if digit == 52 || digit == 56 then End
  else Unknown

-- After `ESC O`: one more byte.
def Key.ss3: List Nat → Key.Decoded
  | [] => Incomplete
  | [final, ..rest] => Got (Key.ofFinal final) rest

-- A byte of 128 or more, leading a UTF-8 character of two to four bytes.
def Key.utf8Lead (lead: Nat) (rest: List Nat): Key.Decoded :=
  if 194 ≤ lead && lead ≤ 223 then Key.utf8More 128 (lead - 192) 1 rest
  else if 224 ≤ lead && lead ≤ 239 then Key.utf8More 2048 (lead - 224) 2 rest
  else if 240 ≤ lead && lead ≤ 244 then Key.utf8More 65536 (lead - 240) 3 rest
  else Got Unknown rest

-- `count` more continuation bytes (128 to 191), each adding six bits to
-- `code`. A code below `minimum` is an overlong form, so `Unknown`. A byte
-- that isn't a continuation ends the character as `Unknown`, and starts the
-- next key.
def Key.utf8More (minimum: Nat) (code: Nat): Nat → List Nat → Key.Decoded
  | 0, rest =>
    if code < minimum then Got Unknown rest else Got (Option.fold (Char.fromNat code) Unknown Printable) rest
  | Succ count, [] => Incomplete
  | Succ count, [byte, ..rest] =>
    if 128 ≤ byte && byte ≤ 191 then Key.utf8More minimum (code * 64 + (byte - 128)) count rest
    else Got Unknown (Cons byte rest)

-- The bytes a terminal sends for a key: what `Key.next` reads back
-- (`Key.nextBytes`). A `Ctrl` with something other than a lower-case
-- letter, which no terminal sends, gives the bytes of `Unknown`: 255, which
-- is never part of UTF-8.
def Key.bytes: Key → List Nat
  | Printable char => Char.utf8 char
  | Enter => [13]
  | Tab => [9]
  | Backspace => [127]
  | Escape => [27]
  | Delete => [27, 91, 51, 126]
  | Up => [27, 91, 65]
  | Down => [27, 91, 66]
  | Right => [27, 91, 67]
  | Left => [27, 91, 68]
  | Home => [27, 91, 72]
  | End => [27, 91, 70]
  | PageUp => [27, 91, 53, 126]
  | PageDown => [27, 91, 54, 126]
  | Ctrl letter =>
    let code := Char.toNat letter
    if 97 ≤ code && code ≤ 122 then [code - 96] else [255]
  | Unknown => [255]

-- Every key in `bytes`, in order, as many as are complete. For tests and
-- for reading a whole input at once.
def Key.all (bytes: List Nat): List Key := Key.allWithin (List.length bytes) bytes

-- At most `limit` keys (each key takes at least one byte, so the length is
-- enough).
def Key.allWithin: Nat → List Nat → List Key
  | 0, bytes => []
  | Succ limit, bytes =>
    match Key.next bytes with
      | Got key rest => Cons key (Key.allWithin limit rest)
      | Incomplete => []
      | NoBytes => []

-- The round trip a terminal makes: the bytes it sends for a named key, then
-- anything at all, decode to that key and the rest. Not for `Escape`, whose
-- byte also starts the other sequences (`Key.nextEscape` says when it holds),
-- or for the keys with a character, `Printable` and `Ctrl`.
def Key.isNamed: Key → Bool
  | Printable char => False
  | Escape => False
  | Ctrl letter => False
  | _ => True

theorem Key.nextBytes (rest: List Nat): (key: Key) → Key.isNamed key = True → Key.next (List.append (Key.bytes key) rest) = Got key rest
  | Printable char, h => Void.exfalso (Bool.falseNotTrue h)
  | Enter, h => rfl
  | Tab, h => rfl
  | Backspace, h => rfl
  | Escape, h => Void.exfalso (Bool.falseNotTrue h)
  | Delete, h => rfl
  | Up, h => rfl
  | Down, h => rfl
  | Left, h => rfl
  | Right, h => rfl
  | Home, h => rfl
  | End, h => rfl
  | PageUp, h => rfl
  | PageDown, h => rfl
  | Ctrl letter, h => Void.exfalso (Bool.falseNotTrue h)
  | Unknown, h => rfl

-- `Escape` comes back when the next byte isn't `[` or `O`; a lone `ESC` at
-- the end of the bytes is `Incomplete` (the handler decides, §3.2).
theorem Key.nextEscape (byte: Nat) (rest: List Nat) (notCsi: (byte == 91) = False) (notSs3: (byte == 79) = False):
    Key.next (List.append (Key.bytes Escape) (Cons byte rest)) = Got Escape (Cons byte rest) :=
  rewrite notCsi, notSs3 in rfl

theorem Key.nextLoneEscape: Key.next (Key.bytes Escape) = Incomplete := rfl

-- Tests: every key, as a terminal sends it.
test "Key: letters, arrows, Ctrl, Enter" :=
  Key.all [97, 27, 91, 65, 1, 13, 113] == [Printable 'a', Up, Ctrl 'a', Enter, Printable 'q']
test "Key: space and the printable ends" := Key.all [32, 33, 126] == [Printable ' ', Printable '!', Printable '~']
test "Key: control bytes" :=
  Key.all [13, 10, 9, 127, 8, 26, 0, 28, 31] == [Enter, Enter, Tab, Backspace, Backspace, Ctrl 'z', Unknown, Unknown, Unknown]
test "Key: piped CR LF is two Enters" := Key.all [13, 10] == [Enter, Enter]
test "Key: the CSI arrows, Home and End" :=
  Key.all [27, 91, 65, 27, 91, 66, 27, 91, 67, 27, 91, 68, 27, 91, 72, 27, 91, 70] == [Up, Down, Right, Left, Home, End]
test "Key: the SS3 arrows, Home and End" :=
  Key.all [27, 79, 65, 27, 79, 66, 27, 79, 67, 27, 79, 68, 27, 79, 72, 27, 79, 70] == [Up, Down, Right, Left, Home, End]
test "Key: the tilde keys" :=
  Key.all [27, 91, 51, 126, 27, 91, 53, 126, 27, 91, 54, 126, 27, 91, 49, 126, 27, 91, 52, 126, 27, 91, 55, 126, 27, 91, 56, 126] ==
    [Delete, PageUp, PageDown, Home, End, Home, End]
test "Key: ESC then a letter is Escape, then the letter" := Key.all [27, 120] == [Escape, Printable 'x']
test "Key: ESC ESC [ A is Escape, then Up" := Key.all [27, 27, 91, 65] == [Escape, Up]
test "Key: a lone ESC is incomplete" :=
  match Key.next [27] with
    | Incomplete => True
    | _ => False
test "Key: a cut-off CSI is incomplete" :=
  match Key.next [27, 91, 49, 59] with
    | Incomplete => True
    | _ => False
test "Key: a cut-off SS3 is incomplete" :=
  match Key.next [27, 79] with
    | Incomplete => True
    | _ => False
test "Key: no bytes" :=
  match Key.next [] with
    | NoBytes => True
    | _ => False
test "Key: Ctrl-Up is one Unknown" := Key.all [27, 91, 49, 59, 53, 65, 120] == [Unknown, Printable 'x']
test "Key: an unknown final byte" := Key.all [27, 91, 90, 27, 79, 80] == [Unknown, Unknown]
test "Key: an unknown tilde key" := Key.all [27, 91, 50, 126, 27, 91, 50, 52, 126] == [Unknown, Unknown]
test "Key: a control byte inside CSI ends it" := Key.all [27, 91, 13] == [Unknown, Enter]
test "Key: UTF-8 of each length" :=
  Key.all [195, 169, 226, 130, 172, 240, 159, 152, 128] == [Printable 'é', Printable '€', Printable '😀']
test "Key: a UTF-8 character cut off is incomplete" :=
  match Key.next [226, 130] with
    | Incomplete => True
    | _ => False
test "Key: bad UTF-8 bytes are Unknown" :=
  Key.all [255, 128, 192, 175, 195, 120, 237, 160, 128, 244, 144, 128, 128, 224, 128, 128] ==
    [Unknown, Unknown, Unknown, Unknown, Unknown, Printable 'x', Unknown, Unknown, Unknown]
test "Key: bytes of every named key decode back" :=
  List.all [Enter, Tab, Backspace, Delete, Up, Down, Left, Right, Home, End, PageUp, PageDown, Unknown] (key => Key.all (Key.bytes key) == [key])
test "Key: bytes of characters and Ctrl decode back" :=
  List.all [Printable 'a', Printable 'é', Printable '€', Printable '😀', Ctrl 'a', Ctrl 'c', Ctrl 'z'] (key => Key.all (Key.bytes key) == [key])
test "Key: Ctrl with a letter that is also a named key" := Key.all (Key.bytes (Ctrl 'm')) == [Enter]

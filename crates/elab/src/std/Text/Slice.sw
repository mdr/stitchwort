--| Reading a text by position: [`Text.slice`], [`Text.getOr`] and
--| [`Text.getLt`], beside [`Text.get`], [`Text.take`] and [`Text.drop`], with
--| their lemmas. Positions count characters (scalar values) from 0, as
--| [`Text.toList`] numbers them.
--|
--| **Cost.** When a program runs (`stitchwort run`, `--native`, a built
--| executable), a text is a shared buffer of characters with a start and a
--| length, so `get`, `getOr`, `getLt`, `slice`, `take`, `drop`, `uncons` and
--| `length` take O(1), and a slice shares its text's characters rather than
--| copying them. A slice keeps the whole buffer alive, except that one of at
--| most 32 characters, from a buffer of 1,024 or more, is copied. To proofs,
--| as everywhere, a text is its list of characters, and each operation here
--| is defined on that list (docs/proposals/file-io-and-text.md §4).
-- A file of its own, so that programs using `take` and `drop` don't check
-- these lemmas.

--| The characters from position `from` up to, not including, `to`:
--| `"hello".slice 1 3` is `"el"`. It stops at the end of the text, and is
--| empty when `to ≤ from`. Slices cut at increasing positions join back into
--| the text ([`Text.sliceAppend`]).
def Text.slice (text: Text) (from to: Nat): Text := text.drop from |> .take (to - from)

--| The character at `index`, or `fallback` past the end. As [`List.getOr`]
--| on [`Text.toList`].
def Text.getOr (text: Text) (index: Nat) (fallback: Char): Char := text.toList.getOr index fallback

--| The character at an index in range, with the proof found by `auto` or
--| passed by name: `text.getLt i` when `i < text.length` is known, so no
--| fallback is needed. As [`List.getLt`] on [`Text.toList`].
def Text.getLt (text: Text) (index: Nat) [auto ok: index < text.length]: Char := List.getLt text.toList index [ok := ok]

theorem Text.sliceToList ∀ (text: Text) (from to: Nat):
    (text.slice from to).toList = (text.toList.drop from).take (to - from) :=
  rfl

--| Ending within the text, a slice has `to - from` characters (none when
--| `to < from`).
theorem Text.lengthSlice ∀ (text: Text) (from to: Nat)
    (within: to ≤ text.length):
    (text.slice from to).length = to - from :=
  List.lengthTake
    (text.toList.drop from)
    (to - from)
    (if ordered: from ≤ to then omega [List.lengthDrop text.toList from (omega)] else omega)

--| Two slices that meet join into one: the lexer's theorem in miniature,
--| since tokens cut at increasing positions and joined give back the text.
theorem Text.sliceAppend ∀ (text: Text) (from middle to: Nat)
    (first: from ≤ middle)
    (second: middle ≤ to):
    text.slice from middle ++ text.slice middle to = text.slice from to :=
  let meet: List.drop text.toList middle = List.drop (List.drop text.toList from) (middle - from) :=
    rewrite <- List.dropAdd from (middle - from) text.toList in rewrite (omega: from + (middle - from) = middle) in rfl
  let counts: middle - from + (to - middle) = to - from := omega
  let lists: List.append
    (List.take (List.drop text.toList from) (middle - from))
    (List.take (List.drop text.toList middle) (to - middle))
    = List.take (List.drop text.toList from) (to - from) :=
    rewrite meet in
      rewrite <- counts in Eq.sym (List.takeAdd (List.drop text.toList from) (middle - from) (to - middle))
  Eq.cong Text.fromList lists

--| The slice from 0 to the length is the whole text.
theorem Text.sliceAll ∀ (text: Text): text.slice 0 text.length = text :=
  Eq.trans
    (Eq.cong Text.fromList (List.takeAll text.toList text.length (Nat.leRefl text.length)))
    (Text.fromToList text)

--| Position `i` of a slice is position `from + i` of the text, within the
--| slice.
theorem Text.getSlice ∀ (text: Text) (from to i: Nat)
    (inside: i < to - from):
    (text.slice from to).get i = text.get (from + i) :=
  Eq.trans (List.getTake (text.toList.drop from) (to - from) i inside) (List.getDrop text.toList from i)

--| `getOr` is `get` with the fallback for `None`.
theorem Text.getOrGet ∀ (text: Text) (i: Nat) (fallback: Char):
    text.getOr i fallback = (text.get i).getOrElse fallback :=
  List.getOrGet text.toList i fallback

--| `getLt` finds what `get` finds.
theorem Text.getLtGet ∀ (text: Text) (i: Nat) (ok: i < text.length): text.get i = Some (text.getLt i [ok := ok]) :=
  List.getLtGet text.toList i ok

test "Text.slice" :=
  "hello".slice 1 3 == "el"
    ∧ "hello".slice 3 10 == "lo"
    ∧ "hello".slice 3 1 == ""
    ∧ "hello".slice 7 9 == ""
    ∧ "h\u{E9}\u{2192}\u{1F600}!".slice 1 4 == "\u{E9}\u{2192}\u{1F600}"

test "Text.getOr and Text.getLt" :=
  "abc".getOr 1 '?' == 'b' ∧ "abc".getOr 3 '?' == '?' ∧ "a\u{1F600}c".getLt 1 == '\u{1F600}'

--| `Text`: the type, conversion to and from lists of characters,
--| decidable equality, comparison, and [`Nat.toText`].
-- Loaded with the core: `Text` is pinned by content hash in the JS backend, and
-- the `Show` instances need `Nat.toText` and `Text.compare`
-- (docs/proposals/prelude-slim.md §2.1).

-- Text (docs/proposals/text-and-io.md)

--| A sequence of Unicode scalar values. `"héllo"` is a `Text`. Equality and
--| ordering compare the sequence exactly, by scalar value, and length counts
--| scalar values; nothing is normalised, so `"\u{E9}"` and `"e\u{301}"` are
--| different texts. Code that goes through [`Text.toList`] and [`Text.fromList`]
--| and their lemmas, rather than `MkText`, won't depend on the representation.
type Text: Type =
  | MkText (chars: List Char)

--| The characters of the text, in order.
def Text.toList: (text: Text) → List Char
  | MkText cs => cs

--| The text of the characters, in order; [`Text.toList`] undoes it (`Text.toFromList`).
def Text.fromList (cs: List Char): Text := MkText cs

theorem Text.fromToList ∀ (t: Text): Text.fromList (Text.toList t) = t := match t with
  | MkText cs => rfl

--| `a ++ b`: the characters of `a`, then those of `b` (`Text.lengthAppend`).
def Text.append (a: Text) (b: Text): Text := MkText (List.append (Text.toList a) (Text.toList b))

--| A decision whether two texts are equal, from one on their characters: its
--| test is theirs.
def Text.decEqFrom (a: Text) (b: Text) (listEq: Decidable (Text.toList a = Text.toList b)): Decidable (a = b) :=
  Decidable.map listEq
    (p => Eq.trans (Eq.sym (Text.fromToList a)) (Eq.trans (Eq.cong Text.fromList p) (Text.fromToList b)))
    (Eq.cong Text.toList)

--| Decides whether two texts are equal, character by character.
def Text.decEq (a: Text) (b: Text): Decidable (a = b) := Text.decEqFrom a b (List.decEq Char.decEq (Text.toList a) (Text.toList b))

--| Lists of characters compared lexicographically, by scalar value.
def Text.compareChars: (xs: List Char) → (ys: List Char) → Ordering
  | [], [] => Equal
  | [], [y, ..ys] => Less
  | [x, ..xs], [] => Greater
  | [x, ..xs], [y, ..ys] =>
    Ordering.andThen (Nat.compare (Char.toNat x) (Char.toNat y)) (Text.compareChars xs ys)

--| How `a` compares with `b`, lexicographically by scalar value: `"ab"` is `Less` than `"b"`. (Not JavaScript's order, which compares
--| UTF-16 code units: there, "\u{10000}" sorts before "\u{E000}".)
def Text.compare (a: Text) (b: Text): Ordering := Text.compareChars (Text.toList a) (Text.toList b)

-- Numbers as text

--| The character of a decimal digit: `Nat.digitChar 7` is `'7'`.
def Nat.digitChar: (digit: Nat) → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | _ => '9'

--| The digits of `n` in front of `acc`. `fuel` keeps it structurally
--| recursive; `n + 1` is always enough.
@[tailrec]
def Nat.digitsOnto: (fuel: Nat) → (n: Nat) → (acc: List Char) → List Char
  | Zero, n, acc => acc
  | Succ fuel, n, acc =>
    if Nat.leq n 9 then [Nat.digitChar n, ..acc] else Nat.digitsOnto fuel (n / 10) [Nat.digitChar (n % 10), ..acc]

--| The number in decimal, without leading zeros: `Nat.toText 42` is `"42"`.
def Nat.toText (n: Nat): Text := MkText (Nat.digitsOnto (Succ n) n [])

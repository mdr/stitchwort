-- Text functions that were in the core (docs/proposals/prelude-slim.md stage 3):
-- the text natives no compiler path names, and the helpers they need. This file
-- depends on the core alone (and `Option.map`), so a program that splits or
-- trims text doesn't also load the lemmas in `Text.sw`.

-- The number of scalar values.
def Text.length (t: Text): Nat := List.length (Text.toList t)

def Text.isEmpty: Text -> Bool
  | MkText Nil         => True
  | MkText (Cons c cs) => False

-- The first character and the rest, unless the text is empty.
def Text.uncons: Text -> Option (Pair Char Text)
  | MkText Nil         => None
  | MkText (Cons c cs) => Some (MkPair c (MkText cs))

def Text.foldChars (f: Char -> b -> b) (z: b): List Char -> b
  | Nil       => z
  | Cons c cs => f c (Text.foldChars f z cs)

-- `Text.fold f z "abc"` is `f 'a' (f 'b' (f 'c' z))`.
def Text.fold (f: Char -> b -> b) (z: b) (t: Text): b := Text.foldChars f z (Text.toList t)

-- Whitespace, for `Text.trim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
def Char.isSpaceCode: Nat -> Bool
  | 9  => True
  | 10 => True
  | 11 => True
  | 12 => True
  | 13 => True
  | 32 => True
  | _  => False

def Char.isSpace (c: Char): Bool := Char.isSpaceCode (Char.toNat c)

def Text.dropSpaces: List Char -> List Char
  | Nil       => Nil
  | Cons c cs => if Char.isSpace c then Text.dropSpaces cs else Cons c cs

-- Removes whitespace (as `Char.isSpace` defines it) from both ends.
def Text.trim (t: Text): Text := MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList t)) Nil)) Nil)

def Char.digitValue (c: Char): Option Nat := if Nat.leq 48 (Char.toNat c) then (if Nat.leq (Char.toNat c) 57 then Some (Char.toNat c - 48) else None) else None

def Text.readDigits (acc: Nat): List Char -> Option Nat
  | Nil       => Some acc
  | Cons c cs => Option.flatMap (d => Text.readDigits (acc * 10 + d) cs) (Char.digitValue c)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `Text.toNat (Nat.toText n) = Some n` but `"007"` reads as 7.
def Text.toNat: Text -> Option Nat
  | MkText Nil         => None
  | MkText (Cons c cs) => Text.readDigits 0 (Cons c cs)

-- An optional `-`, then one or more ASCII digits, and nothing else. Leading
-- zeros are fine and `"-0"` is `0`; `"-"`, `""` and `"+5"` are `None`.
def Text.toInt: Text -> Option Int
  | MkText Nil         => None
  | MkText (Cons c cs) =>
    if Nat.equal (Char.toNat c) 45
    then Option.map (n => Int.neg (OfNat n)) (Text.toNat (MkText cs))
    else Option.map OfNat (Text.toNat (MkText (Cons c cs)))

-- Splitting and joining

-- `Text.splitChars s cs` is the first field and the rest: never empty.
def Text.splitCons (s: Char) (c: Char): Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
  | True,  MkPair f fs => MkPair Nil (Cons f fs)
  | False, MkPair f fs => MkPair (Cons c f) fs

def Text.splitChars (s: Char): List Char -> Pair (List Char) (List (List Char))
  | Nil       => MkPair Nil Nil
  | Cons c cs => Text.splitCons s c (Decidable.toBool (Char.decEq c s)) (Text.splitChars s cs)

def Text.joinChars (s: Char) (f: List Char): List (List Char) -> List Char
  | Nil       => f
  | Cons g gs => List.append f (Cons s (Text.joinChars s g gs))

def Text.textsOf: List (List Char) -> List Text
  | Nil       => Nil
  | Cons f fs => Cons (MkText f) (Text.textsOf fs)

def Text.charListsOf: List Text -> List (List Char)
  | Nil       => Nil
  | Cons t ts => Cons (Text.toList t) (Text.charListsOf ts)

def Text.splitTexts: Pair (List Char) (List (List Char)) -> List Text
  | MkPair f fs => Cons (MkText f) (Text.textsOf fs)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
def Text.split (s: Char) (t: Text): List Text := Text.splitTexts (Text.splitChars s (Text.toList t))

-- The texts with `s` between them. `Text.join s (Text.split s t) = t`.
def Text.join (s: Char): List Text -> Text
  | Nil       => MkText Nil
  | Cons t ts => MkText (Text.joinChars s (Text.toList t) (Text.charListsOf ts))

-- Words: the runs of non-whitespace (as `Char.isSpace` defines it) between
-- runs of whitespace, with no empty ones. `Text.wordsChars cs` is the word
-- that `cs` starts with (so far) and the finished words after it.
def Text.wordsClose: List Char -> List (List Char) -> List (List Char)
  | Nil,       ws => ws
  | Cons c cs, ws => Cons (Cons c cs) ws

def Text.wordsStep (c: Char): Bool -> Pair (List Char) (List (List Char)) -> Pair (List Char) (List (List Char))
  | True,  MkPair w ws => MkPair Nil (Text.wordsClose w ws)
  | False, MkPair w ws => MkPair (Cons c w) ws

def Text.wordsChars: List Char -> Pair (List Char) (List (List Char))
  | Nil       => MkPair Nil Nil
  | Cons c cs => Text.wordsStep c (Char.isSpace c) (Text.wordsChars cs)

def Text.wordsFinish: Pair (List Char) (List (List Char)) -> List Text
  | MkPair w ws => Text.textsOf (Text.wordsClose w ws)

-- `"a  b".words` is `["a", "b"]`, where `"a  b".split ' '` is `["a", "", "b"]`;
-- `"".words` and `"  ".words` are `[]`. Splits on any whitespace, not only
-- spaces.
def Text.words (t: Text): List Text := Text.wordsFinish (Text.wordsChars (Text.toList t))

-- Text functions that were in the core (docs/proposals/prelude-slim.md stage 3):
-- the text natives no compiler path names, and the helpers they need. This file
-- depends on the core alone (and `Option.map`), so a program that splits or
-- trims text doesn't also load the lemmas in `Text.sw`.

-- The number of scalar values.
def Text.length (text: Text): Nat := List.length (Text.toList text)

def Text.isEmpty: Text → Bool
  | MkText Nil => True
  | MkText (Cons char chars) => False

-- The first character and the rest, unless the text is empty.
def Text.uncons: Text → Option (Pair Char Text)
  | MkText Nil => None
  | MkText (Cons char chars) => Some (MkPair char (MkText chars))

def Text.foldChars (f: Char → b → b) (initial: b): List Char → b
  | Nil => initial
  | Cons char chars => f char (Text.foldChars f initial chars)

-- `Text.fold "abc" initial f` is `f 'a' (f 'b' (f 'c' initial))`.
def Text.fold (text: Text) (initial: b) (f: Char → b → b): b := Text.foldChars f initial (Text.toList text)

-- Whitespace, for `Text.trim`: exactly space, tab, line feed, vertical tab,
-- form feed and carriage return. Not Unicode's `White_Space`.
def Char.isSpaceCode: Nat → Bool
  | 9 => True
  | 10 => True
  | 11 => True
  | 12 => True
  | 13 => True
  | 32 => True
  | _ => False

def Char.isSpace (char: Char): Bool := Char.isSpaceCode (Char.toNat char)

def Text.dropSpaces: List Char → List Char
  | Nil => Nil
  | Cons char chars => if Char.isSpace char then Text.dropSpaces chars else Cons char chars

-- Removes whitespace (as `Char.isSpace` defines it) from both ends.
def Text.trim (text: Text): Text := MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList text)) Nil)) Nil)

def Char.digitValue (char: Char): Option Nat := if Nat.leq 48 (Char.toNat char) then (if Nat.leq (Char.toNat char) 57 then Some (Char.toNat char - 48) else None) else None

def Text.readDigits (acc: Nat): List Char → Option Nat
  | Nil => Some acc
  | Cons char chars => Option.flatMap (Char.digitValue char) (digit => Text.readDigits (acc * 10 + digit) chars)

-- A non-empty sequence of ASCII digits, and nothing else: no sign,
-- whitespace or separators. Leading zeros are allowed, so
-- `Text.toNat (Nat.toText n) = Some n` (`Text.toNatToText`) but `"007"`
-- reads as 7.
def Text.toNat: Text → Option Nat
  | MkText Nil => None
  | MkText (Cons char chars) => Text.readDigits 0 (Cons char chars)

-- An optional `-`, then one or more ASCII digits, and nothing else. Leading
-- zeros are fine and `"-0"` is `0`; `"-"`, `""` and `"+5"` are `None`.
def Text.toInt: Text → Option Int
  | MkText Nil => None
  | MkText (Cons char chars) =>
    if Nat.equal (Char.toNat char) 45
    then Option.map (Text.toNat (MkText chars)) (n => Int.neg (OfNat n))
    else Option.map (Text.toNat (MkText (Cons char chars))) OfNat

-- Splitting and joining

-- `Text.splitChars separator chars` is the first field and the rest: never empty.
def Text.splitCons (separator: Char) (char: Char): Bool → Pair (List Char) (List (List Char)) → Pair (List Char) (List (List Char))
  | True, MkPair field fields => MkPair Nil (Cons field fields)
  | False, MkPair field fields => MkPair (Cons char field) fields

def Text.splitChars (separator: Char): List Char → Pair (List Char) (List (List Char))
  | Nil => MkPair Nil Nil
  | Cons char chars => Text.splitCons separator char (Decidable.toBool (Char.decEq char separator)) (Text.splitChars separator chars)

def Text.joinChars (separator: Char) (field: List Char): List (List Char) → List Char
  | Nil => field
  | Cons nextField laterFields => List.append field (Cons separator (Text.joinChars separator nextField laterFields))

def Text.textsOf: List (List Char) → List Text
  | Nil => Nil
  | Cons field fields => Cons (MkText field) (Text.textsOf fields)

def Text.charListsOf: List Text → List (List Char)
  | Nil => Nil
  | Cons text texts => Cons (Text.toList text) (Text.charListsOf texts)

def Text.splitTexts: Pair (List Char) (List (List Char)) → List Text
  | MkPair field fields => Cons (MkText field) (Text.textsOf fields)

-- The fields between separators, keeping empty ones: splitting "a,,b" on
-- ',' gives ["a", "", "b"], and splitting "" gives [""].
def Text.split (text: Text) (separator: Char): List Text := Text.splitTexts (Text.splitChars separator (Text.toList text))

-- The texts with `separator` between them. `Text.join (Text.split text separator) separator = text`.
def Text.join: List Text → (separator: Char) → Text
  | Nil, separator => MkText Nil
  | Cons text texts, separator => MkText (Text.joinChars separator (Text.toList text) (Text.charListsOf texts))

-- The same with a `Text` separator: `Text.joinWith ["a", "b"] ", "` is `"a, b"`
-- (written like `Text.join`, with the list first, so no dot notation).
def Text.joinTextChars (separator: List Char) (field: List Char): List (List Char) → List Char
  | Nil => field
  | Cons nextField laterFields => List.append field (List.append separator (Text.joinTextChars separator nextField laterFields))

@[noReceiver]
def Text.joinWith: List Text → (separator: Text) → Text
  | Nil, separator => MkText Nil
  | Cons text texts, separator => MkText (Text.joinTextChars (Text.toList separator) (Text.toList text) (Text.charListsOf texts))

-- Words: the runs of non-whitespace (as `Char.isSpace` defines it) between
-- runs of whitespace, with no empty ones. `Text.wordsChars chars` is the word
-- that `chars` starts with (so far) and the finished words after it.
def Text.wordsClose: List Char → List (List Char) → List (List Char)
  | Nil, words => words
  | Cons char chars, words => Cons (Cons char chars) words

def Text.wordsStep (char: Char): Bool → Pair (List Char) (List (List Char)) → Pair (List Char) (List (List Char))
  | True, MkPair word words => MkPair Nil (Text.wordsClose word words)
  | False, MkPair word words => MkPair (Cons char word) words

-- Reads `reversed`, the characters last first, onto `st`: a loop, so it is
-- stack-safe on long texts.
def Text.wordsFrom (st: Pair (List Char) (List (List Char))): List Char → Pair (List Char) (List (List Char))
  | Nil => st
  | Cons char reversed => Text.wordsFrom (Text.wordsStep char (Char.isSpace char) st) reversed

def Text.wordsChars (chars: List Char): Pair (List Char) (List (List Char)) := Text.wordsFrom (MkPair Nil Nil) (List.reverseOnto chars Nil)

def Text.wordsFinish: Pair (List Char) (List (List Char)) → List Text
  | MkPair word words => Text.textsOf (Text.wordsClose word words)

-- `"a  b".words` is `["a", "b"]`, where `"a  b".split ' '` is `["a", "", "b"]`;
-- `"".words` and `"  ".words` are `[]`. Splits on any whitespace, not only
-- spaces.
def Text.words (text: Text): List Text := Text.wordsFinish (Text.wordsChars (Text.toList text))

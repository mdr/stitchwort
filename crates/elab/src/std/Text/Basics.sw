-- Text functions that were in the core (docs/proposals/prelude-slim.md stage 3):
-- the text natives no compiler path names, and the helpers they need. This file
-- depends on the core alone (and `Option.map`), so a program that splits or
-- trims text doesn't also load the lemmas in `Text.sw`.

-- The number of scalar values.
def Text.length (text: Text): Nat := text.toList.length

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
def Text.fold (text: Text) (initial: b) (f: Char → b → b): b := Text.foldChars f initial text.toList

-- ASCII whitespace: exactly space, tab, line feed, vertical tab, form feed and
-- carriage return. For layout-sensitive parsing; `Char.isWhitespace` is the
-- Unicode test that `Text.trim` and `Text.words` use.
def Char.isAsciiSpaceCode: Nat → Bool
  | 9 => True
  | 10 => True
  | 11 => True
  | 12 => True
  | 13 => True
  | 32 => True
  | _ => False

def Char.isAsciiSpace (char: Char): Bool := char.toNat |> Char.isAsciiSpaceCode

-- The non-ASCII `White_Space` code points below U+2000: U+0085, U+00A0, U+1680.
def Char.isWhitespaceLow: Nat → Bool
  | 133 => True
  | 160 => True
  | 5760 => True
  | _ => False

-- The `White_Space` code points above U+200A: U+2028, U+2029, U+202F, U+205F,
-- U+3000.
def Char.isWhitespaceHigh: Nat → Bool
  | 8232 => True
  | 8233 => True
  | 8239 => True
  | 8287 => True
  | 12288 => True
  | _ => False

-- Unicode's `White_Space` property: the 25 code points U+0009..U+000D, U+0020,
-- U+0085, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F, U+205F and
-- U+3000 (https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt). This is
-- Rust's `char::is_whitespace`. It differs from JavaScript's `trim` set, which
-- adds U+FEFF (the byte order mark, a format character, not whitespace here)
-- and omits U+0085.
def Char.isWhitespaceCode (code: Nat): Bool :=
  if Nat.leq 8192 code then (if Nat.leq code 8202 then True else Char.isWhitespaceHigh code)
  else (if Nat.leq code 32 then Char.isAsciiSpaceCode code else Char.isWhitespaceLow code)

def Char.isWhitespace (char: Char): Bool := char.toNat |> Char.isWhitespaceCode

def Text.dropSpaces: List Char → List Char
  | Nil => Nil
  | Cons char chars => if Char.isWhitespace char then Text.dropSpaces chars else Cons char chars

-- Removes whitespace (as `Char.isWhitespace` defines it) from both ends.
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
    then Text.toNat (MkText chars) |> .map (n => Int.neg (OfNat n))
    else Text.toNat (MkText (Cons char chars)) |> .map OfNat

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
def Text.split (text: Text) (separator: Char): List Text := Text.splitChars separator text.toList |> Text.splitTexts

-- The texts with `separator` between them. `Text.join (Text.split text separator) separator = text`.
def Text.join: List Text → (separator: Char) → Text
  | Nil, separator => MkText Nil
  | Cons text texts, separator => MkText (Text.joinChars separator (Text.toList text) (Text.charListsOf texts))

-- The same with a `Text` separator: `Text.joinWith ["a", "b"] ", "` is `"a, b"`
-- (written like `Text.join`, with the list first; `List.joinWith` pipes).
def Text.joinTextChars (separator: List Char) (field: List Char): List (List Char) → List Char
  | Nil => field
  | Cons nextField laterFields => List.append field (List.append separator (Text.joinTextChars separator nextField laterFields))

@[noReceiver]
def Text.joinWith: List Text → (separator: Text) → Text
  | Nil, separator => MkText Nil
  | Cons text texts, separator => MkText (Text.joinTextChars (Text.toList separator) (Text.toList text) (Text.charListsOf texts))

-- `Text.joinWith` as a function of the list, so it pipes:
-- `[1, 2].map (.toText) |> .joinWith ", "` is `"1, 2"`.
def List.joinWith (texts: List Text) (separator: Text): Text := Text.joinWith texts separator

-- Words: the runs of non-whitespace (as `Char.isWhitespace` defines it) between
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
  | Cons char reversed => Text.wordsFrom (Text.wordsStep char (Char.isWhitespace char) st) reversed

def Text.wordsChars (chars: List Char): Pair (List Char) (List (List Char)) := Text.wordsFrom (MkPair Nil Nil) (List.reverseOnto chars Nil)

def Text.wordsFinish: Pair (List Char) (List (List Char)) → List Text
  | MkPair word words => Text.textsOf (Text.wordsClose word words)

-- `"a  b".words` is `["a", "b"]`, where `"a  b".split ' '` is `["a", "", "b"]`;
-- `"".words` and `"  ".words` are `[]`. Splits on any whitespace, not only
-- spaces.
def Text.words (text: Text): List Text := Text.wordsChars text.toList |> Text.wordsFinish

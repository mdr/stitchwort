--| Text functions that were in the core: the text natives no compiler path
--| names, and the helpers they need.
-- (docs/proposals/prelude-slim.md stage 3)
-- This file depends on the core alone (and `Option.map`), so a program that
-- splits or trims text doesn't also load the lemmas in `Text.sw`.

--| The number of characters (scalar values): `"héllo".length` is 5.
def Text.length (text: Text): Nat := text.toList.length

--| Whether the text has no characters.
def Text.isEmpty: (text: Text) → Bool
  | MkText [] => True
  | MkText [char, ..chars] => False

--| `text.isEmpty` reads as `text.toList = []`.
@[reading]
theorem Text.isEmptyReads ∀ (text: Text): Text.isEmpty text ↔ text.toList = [] := match text with
  | MkText [] => { forward = h => rfl, backward = h => rfl }
  | MkText [char, ..chars] => {
    forward = h => Void.exfalso (Bool.falseNotTrue h),
    backward = h => Void.exfalso (List.consNotNil char chars h)
  }

--| The first character and the rest, unless the text is empty.
def Text.uncons: (text: Text) → Option (Pair Char Text)
  | MkText [] => None
  | MkText [char, ..chars] => Some (MkPair char (MkText chars))

--| Right fold over a list of characters, as `Text.fold` does it.
def Text.foldChars (f: Char → b → b) (initial: b): (chars: List Char) → b
  | [] => initial
  | [char, ..chars] => f char (Text.foldChars f initial chars)

--| Right fold over the characters: `Text.fold "abc" initial f` is `f 'a' (f 'b' (f 'c' initial))`.
def Text.fold (text: Text) (initial: b) (f: Char → b → b): b := Text.foldChars f initial text.toList

--| Whether a code is ASCII whitespace: exactly space, tab, line feed, vertical
--| tab, form feed and carriage return. For layout-sensitive parsing;
--| `Char.isWhitespace` is the Unicode test that `Text.trim` and `Text.words` use.
def Char.isAsciiSpaceCode: (code: Nat) → Bool := matches
  | 9
  | 10
  | 11
  | 12
  | 13
  | 32

--| Whether a character is ASCII whitespace: space, tab, line feed, vertical tab, form feed or carriage return.
def Char.isAsciiSpace (char: Char): Bool := char.toNat |> Char.isAsciiSpaceCode

--| Whether a character is an ASCII lowercase letter, `a` to `z`.
def Char.isAsciiLowercase (char: Char): Bool := 'a' ≤ char ≤ 'z'

--| Whether a character is an ASCII uppercase letter, `A` to `Z`.
def Char.isAsciiUppercase (char: Char): Bool := 'A' ≤ char ≤ 'Z'

--| Whether a code is one of the non-ASCII `White_Space` code points below U+2000: U+0085, U+00A0, U+1680.
def Char.isWhitespaceLow: (code: Nat) → Bool := matches
  | 133
  | 160
  | 5760

--| Whether a code is one of the `White_Space` code points above U+200A: U+2028,
--| U+2029, U+202F, U+205F, U+3000.
def Char.isWhitespaceHigh: (code: Nat) → Bool := matches
  | 8232
  | 8233
  | 8239
  | 8287
  | 12288

--| Whether a code has Unicode's `White_Space` property. That is the 25 code
--| points U+0009..U+000D, U+0020, U+0085, U+00A0, U+1680, U+2000..U+200A,
--| U+2028, U+2029, U+202F, U+205F and U+3000
--| (https://www.unicode.org/Public/UCD/latest/ucd/PropList.txt). This is
--| Rust's `char::is_whitespace`. It differs from JavaScript's `trim` set, which
--| adds U+FEFF (the byte order mark, a format character, not whitespace here)
--| and omits U+0085.
def Char.isWhitespaceCode (code: Nat): Bool :=
  if Nat.leq 8192 code then (if Nat.leq code 8202 then True else Char.isWhitespaceHigh code)
  else (if Nat.leq code 32 then Char.isAsciiSpaceCode code else Char.isWhitespaceLow code)

--| Whether a character is whitespace, by Unicode's `White_Space` property (Rust's `char::is_whitespace`).
def Char.isWhitespace (char: Char): Bool := char.toNat |> Char.isWhitespaceCode

--| The characters without the whitespace at their start.
@[tailrec]
def Text.dropSpaces: (chars: List Char) → List Char
  | [] => []
  | [char, ..chars] => if Char.isWhitespace char then Text.dropSpaces chars else [char, ..chars]

--| The text without whitespace (as `Char.isWhitespace` defines it) at either end:
--| its last character isn't whitespace ([`Text.trimLast`]).
def Text.trim (text: Text): Text := MkText (List.reverseOnto (Text.dropSpaces (List.reverseOnto (Text.dropSpaces (Text.toList text)) [])) [])

--| The value of an ASCII digit: `Char.digitValue '7'` is `Some 7`, and a non-digit gives `None`.
def Char.digitValue (char: Char): Option Nat := if Nat.leq 48 (Char.toNat char) then (if Nat.leq (Char.toNat char) 57 then Some (Char.toNat char - 48) else None) else None

--| Whether a character is an ASCII digit, `0` to `9`: `Char.isAsciiDigit '7'` is `True`.
--| It is a range test on the code, with no `Option` to unpack;
--| [`Char.isAsciiDigitDigitValue`] says it agrees with `Char.digitValue`.
def Char.isAsciiDigit (char: Char): Bool := 48 <= char.toNat <= 57

--| `Char.isAsciiDigit` holds exactly when `Char.digitValue` gives a value.
theorem Char.isAsciiDigitDigitValue ∀ (char: Char): char.isAsciiDigit = char.digitValue.isSome :=
  match low: Nat.leq 48 char.toNat with
    | True =>
      match high: Nat.leq char.toNat 57 with
        | True => rfl
        | False => rfl
    | False => rfl

--| The number the ASCII digits spell, after the digits already read (`acc`); `None` at a non-digit.
def Text.readDigits (acc: Nat): (chars: List Char) → Option Nat
  | [] => Some acc
  | [char, ..chars] => Option.flatMap (Char.digitValue char) (digit => Text.readDigits (acc * 10 + digit) chars)

--| The number a text of ASCII digits spells: `"42".toNat` is `Some 42`. It
--| must be one or more digits and nothing else: no sign, whitespace or
--| separators. Leading zeros are allowed, so
--| `Text.toNat (Nat.toText n) = Some n` ([`Text.toNatToText`]) but `"007"`
--| reads as 7. What it gives on any text is [`Text.toNatDigits`].
def Text.toNat: (text: Text) → Option Nat
  | MkText [] => None
  | MkText [char, ..chars] => Text.readDigits 0 [char, ..chars]

--| `Text.readDigits` reads every character as a digit or fails: after `acc`
--| it gives the value of `acc` followed by the digits, `Some (foldLeft …)`,
--| when all of `chars` are digits, and `None` otherwise. The loop behind
--| [`Text.toNatDigits`].
theorem Text.readDigitsValue ∀ (acc: Nat) (chars: List Char):
    Text.readDigits acc chars = (if chars.all (char => char.digitValue.isSome) then Some (List.foldLeft (chars.map (digit => digit.digitValue.getOrElse 0)) acc (acc digit => acc * 10 + digit)) else None) :=
  match chars with
    | [] => rfl
    | [char, ..rest] =>
      match value: char.digitValue with
        | None => rfl
        | Some d => Text.readDigitsValue (acc * 10 + d) rest

--| The integer a text spells: an optional `-`, then one or more ASCII digits,
--| and nothing else. Leading zeros are fine and `"-0"` is `0`; `"-"`, `""` and
--| `"+5"` are `None`.
def Text.toInt: (text: Text) → Option Int
  | MkText [] => None
  | MkText [char, ..chars] =>
    if Nat.equal (Char.toNat char) 45
    then Text.toNat (MkText chars) |> .map (n => Int.neg (OfNat n))
    else Text.toNat (MkText [char, ..chars]) |> .map OfNat

-- Splitting and joining

--| One step of `Text.splitChars`: `char` starts a new field if it is the separator, or joins the first field.
def Text.splitCons (separator: Char) (char: Char): (isSeparator: Bool) → (state: Pair (List Char) (List (List Char))) → Pair (List Char) (List (List Char))
  | True, MkPair field fields => MkPair [] [field, ..fields]
  | False, MkPair field fields => MkPair [char, ..field] fields

--| The first field of the characters and the fields after it, split at each `separator`.
def Text.splitChars (separator: Char): (chars: List Char) → Pair (List Char) (List (List Char))
  | [] => MkPair [] []
  | [char, ..chars] => Text.splitCons separator char (Decidable.holds (Char.decEq char separator)) (Text.splitChars separator chars)

--| The fields joined into one list of characters, `separator` between each two.
def Text.joinChars (separator: Char) (field: List Char): (fields: List (List Char)) → List Char
  | [] => field
  | [nextField, ..laterFields] => List.append field [separator, ..Text.joinChars separator nextField laterFields]

--| Each list of characters as a text.
def Text.textsOf: (fields: List (List Char)) → List Text
  | [] => []
  | [field, ..fields] => [MkText field, ..Text.textsOf fields]

--| Each text as its list of characters.
def Text.charListsOf: (texts: List Text) → List (List Char)
  | [] => []
  | [text, ..texts] => [Text.toList text, ..Text.charListsOf texts]

--| The fields `Text.splitChars` found, as texts.
def Text.splitTexts: (state: Pair (List Char) (List (List Char))) → List Text
  | MkPair field fields => [MkText field, ..Text.textsOf fields]

--| The fields between separators, keeping empty ones: splitting "a,,b" on
--| ',' gives ["a", "", "b"], and splitting "" gives [""].
def Text.split (text: Text) (separator: Char): List Text := Text.splitChars separator text.toList |> Text.splitTexts

--| The texts with `separator` between them: `Text.join (Text.split text separator) separator = text` ([`Text.joinSplit`]).
def Text.join: (texts: List Text) → (separator: Char) → Text
  | [], separator => MkText []
  | [text, ..texts], separator => MkText (Text.joinChars separator (Text.toList text) (Text.charListsOf texts))

--| The fields joined into one list of characters, the characters of `separator` between each two.
def Text.joinTextChars (separator: List Char) (field: List Char): (fields: List (List Char)) → List Char
  | [] => field
  | [nextField, ..laterFields] => List.append field (List.append separator (Text.joinTextChars separator nextField laterFields))

--| The texts with a `Text` separator between them: `Text.joinWith ["a", "b"] ", "` is `"a, b"`.
--| It is written like `Text.join`, with the list first; `List.joinWith` pipes.
@[noReceiver]
def Text.joinWith: (texts: List Text) → (separator: Text) → Text
  | [], separator => MkText []
  | [text, ..texts], separator => MkText (Text.joinTextChars (Text.toList separator) (Text.toList text) (Text.charListsOf texts))

--| `Text.joinWith` as a function of the list, so it pipes:
--| `[1, 2].map (.toText) |> .joinWith ", "` is `"1, 2"`.
def List.joinWith (texts: List Text) (separator: Text): Text := Text.joinWith texts separator

-- Words: the runs of non-whitespace (as `Char.isWhitespace` defines it) between
-- runs of whitespace, with no empty ones. `Text.wordsChars chars` is the word
-- that `chars` starts with (so far) and the finished words after it.

--| The finished words with `word` in front, unless it is empty.
def Text.wordsClose: (word: List Char) → (words: List (List Char)) → List (List Char)
  | [], words => words
  | [char, ..chars], words => [[char, ..chars], ..words]

--| One step of reading words, last character first: whitespace closes the current word, anything else joins it.
def Text.wordsStep (char: Char): (isSpace: Bool) → (state: Pair (List Char) (List (List Char))) → Pair (List Char) (List (List Char))
  | True, MkPair word words => MkPair [] (Text.wordsClose word words)
  | False, MkPair word words => MkPair [char, ..word] words

--| Reads `reversed`, the characters last first, onto `st`: a loop, so it is
--| stack-safe on long texts.
@[tailrec]
def Text.wordsFrom (st: Pair (List Char) (List (List Char))): (chars: List Char) → Pair (List Char) (List (List Char))
  | [] => st
  | [char, ..reversed] => Text.wordsFrom (Text.wordsStep char (Char.isWhitespace char) st) reversed

--| The word the characters start with (so far) and the finished words after it.
def Text.wordsChars (chars: List Char): Pair (List Char) (List (List Char)) := Text.wordsFrom (MkPair [] []) (List.reverseOnto chars [])

--| All the words, with the first one closed, as texts.
def Text.wordsFinish: (state: Pair (List Char) (List (List Char))) → List Text
  | MkPair word words => Text.textsOf (Text.wordsClose word words)

--| The runs of non-whitespace in the text, without empty ones: `"a  b".words` is
--| `["a", "b"]`, where `"a  b".split ' '` is `["a", "", "b"]`. `"".words` and
--| `"  ".words` are `[]`. Splits on any whitespace, not only spaces.
def Text.words (text: Text): List Text := Text.wordsChars text.toList |> Text.wordsFinish

--| What `dropSpaces` leaves doesn't start with whitespace.
theorem Text.dropSpacesHead ∀ (chars: List Char) (first: Char) (rest: List Char) (h: Text.dropSpaces chars = [first, ..rest]):
    Char.isWhitespace first = False := match chars with
      | [char, ..chars] =>
        match space: Char.isWhitespace char with
          | True => Text.dropSpacesHead chars first rest h
          | False => rewrite <- Eq.cong (.headOr first) h in space

--| A trimmed text doesn't end with whitespace.
theorem Text.trimLast ∀ (text: Text) (front: List Char) (last: Char) (h: text.trim.toList = front ++ [last]): Char.isWhitespace last = False :=
  let kept := Text.dropSpaces (List.reverseOnto (Text.dropSpaces text.toList) [])
  let back: List.reverse [last, ..List.reverse front] = front ++ [last] :=
    rewrite List.reverseCons last (List.reverse front), List.reverseReverse front in rfl
  let flipped: kept = [last, ..List.reverse front] :=
    rewrite <- List.reverseReverse kept, <- List.reverseReverse [last, ..List.reverse front], back in Eq.cong List.reverse h
  Text.dropSpacesHead _ last _ flipped

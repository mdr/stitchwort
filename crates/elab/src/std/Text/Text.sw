--| Text beyond the core: the split/join and length lemmas, and `Text.lines`
--| with `IO.readAllLines`.
-- This file was the prelude's "Lines" section and the few text theorems
-- beside it.

theorem Text.toFromList (cs: List Char): Text.toList (Text.fromList cs) = cs := rfl

--| The character at index `i`, counting from 0, or `None` past the end: as
--| [`List.get`] on [`Text.toList`] ([`Text.getToList`]).
def Text.get (text: Text) (i: Nat): Option Char := text.toList.get i

theorem Text.getToList (text: Text) (i: Nat): Text.get text i = List.get text.toList i := rfl

--| How many characters satisfy `p`: as [`List.count`] on [`Text.toList`]
--| ([`Text.countToList`]).
def Text.count (text: Text) (p: Char → Bool): Nat := text.toList.count p

theorem Text.countToList (text: Text) (p: Char → Bool):
    Text.count text p = List.count text.toList p := rfl

--| Whether some character satisfies `p`: as [`List.any`] on [`Text.toList`]
--| ([`Text.anyToList`]).
def Text.any (text: Text) (p: Char → Bool): Bool := text.toList.any p

theorem Text.anyToList (text: Text) (p: Char → Bool):
    Text.any text p = List.any text.toList p := rfl

--| Whether every character satisfies `p`: as [`List.all`] on [`Text.toList`]
--| ([`Text.allToList`]).
def Text.all (text: Text) (p: Char → Bool): Bool := text.toList.all p

theorem Text.allToList (text: Text) (p: Char → Bool):
    Text.all text p = List.all text.toList p := rfl

test "Text.get" := Text.get "abc" 0 == Some 'a' ∧ Text.get "abc" 2 == Some 'c' ∧ Text.get "abc" 3 == None

test "Text.count" := Text.count "banana" (== 'a') == 3 ∧ Text.count "abc" (== 'z') == 0 ∧ Text.count "" (== 'a') == 0

test "Text.any and Text.all" :=
  Text.any "abc" (== 'b') ∧ ¬(Text.any "abc" (== 'z')) ∧ Text.all "aaa" (== 'a') ∧ ¬(Text.all "aba" (== 'a'))

theorem Text.lengthAppend (a: Text) (b: Text):
    Text.length (Text.append a b) = Text.length a + Text.length b := List.lengthAppend (Text.toList a) (Text.toList b)

--| The text made n characters long with copies of `char` after it: `Text.padRight "ab" 5 '.'` is `"ab..."`.
--| It is `text` itself when that is already n long or longer.
def Text.padRight (text: Text) (n: Nat) (char: Char): Text :=
  text.toList.padRight n char |> Text.fromList

theorem Text.padRightExample: Text.padRight "ab" 5 '.' = "ab..." := rfl

theorem Text.padRightLongEnough: Text.padRight "ab" 1 '.' = "ab" := rfl

--| The text made n characters long with copies of `char` before it: `Text.padLeft "7" 2 '0'` is `"07"`.
--| It is `text` itself when that is already n long or longer.
def Text.padLeft (text: Text) (n: Nat) (char: Char): Text :=
  text.toList.padLeft n char |> Text.fromList

theorem Text.padLeftExample: Text.padLeft "7" 2 '0' = "07" := rfl

theorem Text.padLeftLongEnough: Text.padLeft "123" 2 '0' = "123" := rfl

--| Whether `a` comes before `b`, lexicographically by scalar value.
def Text.less (a: Text) (b: Text): Bool := Ordering.isLess (Text.compare a b)

--| A first field and the fields after it, joined with `separator` between each two.
def Text.joinPair (separator: Char): Pair (List Char) (List (List Char)) → List Char
  | MkPair field fields => Text.joinChars separator field fields

theorem Text.joinCons (s: Char) (c: Char) (f: List Char): (fs: List (List Char)) →
    Text.joinChars s (Cons c f) fs = Cons c (Text.joinChars s f fs)
  | Nil => rfl
  | Cons g gs => rfl

theorem Text.joinSplitCons (s: Char) (c: Char) (cs: List Char):
    (p: Pair (List Char) (List (List Char))) → Text.joinPair s p = cs →
    (d: Decidable (c = s)) → Text.joinPair s (Text.splitCons s c (Decidable.toBool d) p) = Cons c cs
  | MkPair f fs, h, Yes e =>
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (x => Cons x cs) (Eq.sym e))
  | MkPair f fs, h, No r =>
    Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars (s: Char): (cs: List Char) → Text.joinPair s (Text.splitChars s cs) = cs
  | Nil => rfl
  | Cons c cs =>
    Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

theorem Text.charListsOfTexts: (fs: List (List Char)) → Text.charListsOf (Text.textsOf fs) = fs
  | Nil => rfl
  | Cons f fs => Eq.cong (Cons f) (Text.charListsOfTexts fs)

theorem Text.joinSplitTexts (s: Char): (p: Pair (List Char) (List (List Char))) →
    Text.join (Text.splitTexts p) s = MkText (Text.joinPair s p)
  | MkPair f fs => Eq.cong (l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit: (t: Text) → (s: Char) → Text.join (Text.split t s) s = t
  | MkText cs, s =>
    Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

-- Lines

--| Whether a code is the line feed, 10.
def Char.isLineFeedCode: Nat → Bool
  | 10 => True
  | _ => False

--| Whether a code is the carriage return, 13.
def Char.isCarriageReturnCode: Nat → Bool
  | 13 => True
  | _ => False

--| A line that ended with a line feed, from its characters newest first,
--| without a carriage return just before the line feed.
def Text.endLine: List Char → Text
  | Nil => MkText Nil
  | Cons char chars => MkText (List.reverseOnto (if Char.isCarriageReturnCode (Char.toNat char) then chars else Cons char chars) Nil)

--| The last line, if the text doesn't end with a line feed: kept whole.
def Text.lastLine: List Char → List Text → List Text
  | Nil, acc => acc
  | Cons c cs, acc => Cons (MkText (List.reverseOnto (Cons c cs) Nil)) acc

--| The lines of the characters, after the current line's characters
--| (`line`, newest first) and the finished lines (`acc`, newest first).
def Text.linesFrom (line: List Char) (acc: List Text): List Char → List Text
  | Nil => List.reverseOnto (Text.lastLine line acc) Nil
  | Cons char chars =>
    if Char.isLineFeedCode (Char.toNat char) then Text.linesFrom Nil (Cons (Text.endLine line) acc) chars
    else Text.linesFrom (Cons char line) acc chars

--| The lines of a text, without their line endings, as Rust's `str:: lines`
--| gives them. A line ends with a line feed, or a carriage return and a line
--| feed; the last line's ending is optional, so "a\nb" and "a\nb\n" both
--| give ["a", "b"], "" gives [], and "\n" gives [""]. A carriage return
--| anywhere else is kept. These are the lines `IO.readLine` would give.
def Text.lines (text: Text): List Text := Text.linesFrom Nil Nil (Text.toList text)

--| Every remaining line of input, in order, as `IO.readLine` would give them.
--| Total: the input is read all at once.
def IO.readAllLines(): {IO} List Text := IO.readAll().lines

-- Prefixes, suffixes and substrings. Characters are Unicode scalar values, as
-- in `Text.length`. The main text comes first, then the prefix, suffix,
-- needle or separator, so `line.stripPrefix "L"`, `line |> Text.stripPrefix
-- "L"` and `Text.stripPrefix line "L"` all mean the same.

--| The first `n` characters of the text (all of it if it is shorter); with `Text.drop`, the whole text ([`Text.takeAppendDrop`]).
def Text.take (text: Text) (n: Nat): Text := text.toList.take n |> Text.fromList

--| The text without its first `n` characters (empty if it is shorter).
def Text.drop (text: Text) (n: Nat): Text := text.toList.drop n |> Text.fromList

--| Whether two characters are the same.
def Text.sameChar (a: Char) (b: Char): Bool := Nat.equal (Char.toNat a) (Char.toNat b)

--| The rest of the characters after the prefix `p`, if they start with it.
def Text.stripPrefixChars: List Char → List Char → Option (List Char)
  | Nil, ys => Some ys
  | Cons p ps, Nil => None
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.stripPrefixChars ps ys else None

--| Whether the second list of characters starts with the first.
def Text.startsWithChars: List Char → List Char → Bool
  | Nil, ys => True
  | Cons p ps, Nil => False
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.startsWithChars ps ys else False

--| The rest of `text` after `prefix`, or `None` if `text` doesn't start with it
--| ([`Text.stripPrefixAppend`]). The empty prefix gives `Some text`.
def Text.stripPrefix (text: Text) (prefix: Text): Option Text :=
  Text.stripPrefixChars prefix.toList text.toList |> .map Text.fromList

--| The text without its ending `suffix`, or `None` if it doesn't end with it.
def Text.stripSuffix (text: Text) (suffix: Text): Option Text :=
  Text.stripPrefixChars suffix.toList.reverse text.toList.reverse |> .map (chars => chars.reverse |> Text.fromList)

--| Whether `text` starts with `prefix` ([`Text.startsWithAppend`]).
def Text.startsWith (text: Text) (prefix: Text): Bool :=
  Text.startsWithChars prefix.toList text.toList

--| Whether `text` ends with `suffix`.
def Text.endsWith (text: Text) (suffix: Text): Bool :=
  Text.startsWithChars suffix.toList.reverse text.toList.reverse

--| Whether `needle` occurs in the list of characters.
def Text.containsChars (needle: List Char): List Char → Bool
  | Nil => Text.startsWithChars needle Nil
  | Cons char chars => if Text.startsWithChars needle (Cons char chars) then True else Text.containsChars needle chars

--| Whether `needle` occurs in the text. The empty text occurs in every text.
def Text.contains (text: Text) (needle: Text): Bool := Text.containsChars needle.toList text.toList

--| The loop of `Text.splitOn`, reading the characters. `cur` is the current
--| piece's characters, newest first, `acc` the finished pieces, newest first,
--| and `skip` how many more characters of a separator just found are still to
--| be passed over. `n` is the separator's length less one.
def Text.splitOnLoop (sep: List Char) (n: Nat) (cur: List Char) (acc: List Text): List Char → Nat → List Text
  | Nil, skip => List.reverseOnto (Cons (MkText (List.reverseOnto cur Nil)) acc) Nil
  | Cons char chars, Succ skip => Text.splitOnLoop sep n cur acc chars skip
  | Cons char chars, Zero =>
    let hit := Text.startsWithChars sep (Cons char chars)
    Text.splitOnLoop sep n
      (if hit then Nil else Cons char cur)
      (if hit then Cons (MkText (List.reverseOnto cur Nil)) acc else acc)
      chars
      (if hit then n else Zero)

--| The characters split at each occurrence of the separator, as `Text.splitOn` does it.
def Text.splitOnChars: List Char → List Char → List Text
  | Nil, chars => Cons (MkText chars) Nil
  | Cons first rest, chars => Text.splitOnLoop (Cons first rest) (List.length rest) Nil Nil chars Zero

--| The pieces between occurrences of the whole separator: `"a--b".splitOn "-"` gives ["a", "", "b"].
--| It scans left to right without overlaps, so
--| `Text.splitOn "aaa" "aa"` gives ["", "a"]. Always at least one piece, and
--| `Text.splitOn text s` of a text without `s` is `[text]`. An empty separator
--| doesn't split: the result is `[text]`, as in Lean's `String.splitOn`.
def Text.splitOn (text: Text) (sep: Text): List Text := Text.splitOnChars sep.toList text.toList

-- Lemmas

theorem Text.sameCharRefl (c: Char): Text.sameChar c c = True := Nat.equalRefl (Char.toNat c)

theorem Text.stripPrefixCharsAppend (t: List Char): (p: List Char) →
    Text.stripPrefixChars p (List.append p t) = Some t
  | Nil => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.stripPrefixChars ps (List.append ps t) else None) (Text.sameCharRefl c))
      (Text.stripPrefixCharsAppend t ps)

theorem Text.stripPrefixAppend (p: Text) (t: Text): Text.stripPrefix (Text.append p t) p = Some t :=
  Eq.trans (Eq.cong (.map Text.fromList) (Text.stripPrefixCharsAppend (Text.toList t) (Text.toList p)))
    (Eq.cong Some (Text.fromToList t))

theorem Text.startsWithCharsAppend (t: List Char): (p: List Char) →
    Text.startsWithChars p (List.append p t) = True
  | Nil => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.startsWithChars ps (List.append ps t) else False) (Text.sameCharRefl c))
      (Text.startsWithCharsAppend t ps)

theorem Text.startsWithAppend (p: Text) (t: Text): Text.startsWith (Text.append p t) p = True :=
  Text.startsWithCharsAppend (Text.toList t) (Text.toList p)

theorem Text.takeDropChars: (n: Nat) → (cs: List Char) → List.append (List.take cs n) (List.drop cs n) = cs
  | Zero, cs => rfl
  | Succ n, Nil => rfl
  | Succ n, Cons c cs => Eq.cong (Cons c) (Text.takeDropChars n cs)

theorem Text.takeAppendDrop (t: Text) (n: Nat): Text.append (Text.take t n) (Text.drop t n) = t :=
  Text.ext (Text.append (Text.take t n) (Text.drop t n)) t (Text.takeDropChars n (Text.toList t))

test "take and drop" := Text.take "héllo" 2 == "hé" ∧ Text.drop "héllo" 2 == "llo"
test "take and drop past the end" := Text.take "ab" 9 == "ab" ∧ Text.drop "ab" 9 == ""
test "stripPrefix" := Text.stripPrefix "L68" "L" == Some "68" ∧ Text.stripPrefix "R68" "L" == None
test "stripSuffix" := Text.stripSuffix "L68" "68" == Some "L" ∧ Text.stripSuffix "L68" "x" == None
test "startsWith and endsWith" := Text.startsWith "abc" "ab" ∧ Text.endsWith "abc" "bc" ∧ ¬(Text.startsWith "abc" "abcd")
test "contains" := Text.contains "abcd" "bc" ∧ ¬(Text.contains "abcd" "ca") ∧ Text.contains "" ""
test "splitOn" := Text.splitOn "a, b" ", " == ["a", "b"] ∧ Text.splitOn "" "x" == [""]
test "splitOn empty separator" := Text.splitOn "abc" "" == ["abc"]
test "splitOn overlapping" := Text.splitOn "aaa" "aa" == ["", "a"]

--| The text n times over: `"ab".repeat 3` is `"ababab"`, and `text.repeat 0` is the empty text.
def Text.repeat (text: Text) (n: Nat): Text := List.replicate n text.toList |> .concat |> Text.fromList

--| The text cut into pieces of `n` characters, the last one shorter if need be:
--| `"abcde".chunksOf 2` is `["ab", "cd", "e"]`. As `List.chunksOf` does for
--| lists, `n = 0` gives the whole text as one chunk (none for an empty text).
def Text.chunksOf (text: Text) (n: Nat): List Text := text.toList.chunksOf n |> .map Text.fromList

test "Text.repeat" := Text.repeat "ab" 3 == "ababab" ∧ Text.repeat "ab" 0 == "" ∧ Text.repeat "" 4 == ""
test "Text.chunksOf" := Text.chunksOf "abcde" 2 == ["ab", "cd", "e"] ∧ Text.chunksOf "" 2 == []
test "Text.chunksOf zero" := Text.chunksOf "abc" 0 == ["abc"]
test "Text.words" := "a  b\tc\n d ".words == ["a", "b", "c", "d"] ∧ "".words == [] ∧ "  ".words == [] ∧ "ab".words == ["ab"]
test "trim removes Unicode White_Space" := Text.trim "\u{A0}\u{3000}x y\u{85}\u{2028}\u{2003}" == "x y"
test "trim keeps the byte order mark" := Text.length (Text.trim "\u{FEFF}x\u{FEFF}") == 3
test "words splits on Unicode White_Space" := "a\u{A0}b\u{3000}c".words == ["a", "b", "c"]
test "isAsciiSpace is ASCII only" := Char.isAsciiSpace ' ' ∧ ¬(Char.isAsciiSpace '\u{A0}') ∧ Char.isWhitespace '\u{A0}' ∧ ¬(Char.isWhitespace '\u{FEFF}')

--| Whether a character is an ASCII letter, `a` to `z` or `A` to `Z`.
def Char.isAsciiLetter (char: Char): Bool :=
  let code := char.toNat
  (97 <= code && code <= 122) || (65 <= code && code <= 90)

--| Whether a character is an ASCII letter or digit.
def Char.isAsciiAlphanumeric (char: Char): Bool := char.isAsciiLetter || char.digitValue.isSome

test "Char.isAsciiLetter" := Char.isAsciiLetter 'a' ∧ Char.isAsciiLetter 'Z' ∧ ¬(Char.isAsciiLetter '0') ∧ ¬(Char.isAsciiLetter '.') ∧ ¬(Char.isAsciiLetter 'é')
test "Char.isAsciiAlphanumeric" := Char.isAsciiAlphanumeric 'q' ∧ Char.isAsciiAlphanumeric '7' ∧ ¬(Char.isAsciiAlphanumeric '#')

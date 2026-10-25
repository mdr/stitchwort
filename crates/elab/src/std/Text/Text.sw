-- Text beyond the core: the split/join and length lemmas, and `Text.lines`
-- with `IO.readAllLines`. This file was the prelude's "Lines" section and
-- the few text theorems beside it.

theorem Text.toFromList (cs: List Char): Text.toList (Text.fromList cs) = cs := rfl

theorem Text.lengthAppend (a: Text) (b: Text):
    Text.length (Text.append a b) = Text.length a + Text.length b := List.lengthAppend (Text.toList a) (Text.toList b)

-- `Text.padRight text n char` is `text` followed by enough copies of `char` to make it
-- n characters long (it is `text` itself when that is already n long or longer).
def Text.padRight (text: Text) (n: Nat) (char: Char): Text :=
  Text.fromList (List.padRight (Text.toList text) n char)

theorem Text.padRightExample: Text.padRight "ab" 5 '.' = "ab..." := rfl

theorem Text.padRightLongEnough: Text.padRight "ab" 1 '.' = "ab" := rfl

def Text.less (a: Text) (b: Text): Bool := Ordering.isLess (Text.compare a b)

def Text.joinPair (separator: Char): Pair (List Char) (List (List Char)) -> List Char
  | MkPair field fields => Text.joinChars separator field fields

theorem Text.joinCons (s: Char) (c: Char) (f: List Char): (fs: List (List Char)) ->
    Text.joinChars s (Cons c f) fs = Cons c (Text.joinChars s f fs)
  | Nil => rfl
  | Cons g gs => rfl

theorem Text.joinSplitCons (s: Char) (c: Char) (cs: List Char):
    (p: Pair (List Char) (List (List Char))) -> Text.joinPair s p = cs ->
    (d: Decidable (c = s)) -> Text.joinPair s (Text.splitCons s c (Decidable.toBool d) p) = Cons c cs
  | MkPair f fs, h, Yes e =>
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (x => Cons x cs) (Eq.sym e))
  | MkPair f fs, h, No r =>
    Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars (s: Char): (cs: List Char) -> Text.joinPair s (Text.splitChars s cs) = cs
  | Nil => rfl
  | Cons c cs =>
    Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

theorem Text.charListsOfTexts: (fs: List (List Char)) -> Text.charListsOf (Text.textsOf fs) = fs
  | Nil => rfl
  | Cons f fs => Eq.cong (Cons f) (Text.charListsOfTexts fs)

theorem Text.joinSplitTexts (s: Char): (p: Pair (List Char) (List (List Char))) ->
    Text.join (Text.splitTexts p) s = MkText (Text.joinPair s p)
  | MkPair f fs => Eq.cong (l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit: (t: Text) -> (s: Char) -> Text.join (Text.split t s) s = t
  | MkText cs, s =>
    Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

-- Lines

def Char.isLineFeedCode: Nat -> Bool
  | 10 => True
  | _ => False

def Char.isCarriageReturnCode: Nat -> Bool
  | 13 => True
  | _ => False

-- A line that ended with a line feed, from its characters newest first,
-- without a carriage return just before the line feed.
def Text.endLine: List Char -> Text
  | Nil => MkText Nil
  | Cons char chars => MkText (List.reverseOnto (if Char.isCarriageReturnCode (Char.toNat char) then chars else Cons char chars) Nil)

-- The last line, if the text doesn't end with a line feed: kept whole.
def Text.lastLine: List Char -> List Text -> List Text
  | Nil, acc => acc
  | Cons c cs, acc => Cons (MkText (List.reverseOnto (Cons c cs) Nil)) acc

-- `line` is the current line's characters, newest first, and `acc` the
-- finished lines, newest first.
def Text.linesFrom (line: List Char) (acc: List Text): List Char -> List Text
  | Nil => List.reverseOnto (Text.lastLine line acc) Nil
  | Cons char chars =>
    if Char.isLineFeedCode (Char.toNat char) then Text.linesFrom Nil (Cons (Text.endLine line) acc) chars
    else Text.linesFrom (Cons char line) acc chars

-- The lines of a text, without their line endings, as Rust's `str:: lines`
-- gives them. A line ends with a line feed, or a carriage return and a line
-- feed; the last line's ending is optional, so "a\nb" and "a\nb\n" both
-- give ["a", "b"], "" gives [], and "\n" gives [""]. A carriage return
-- anywhere else is kept. These are the lines `IO.readLine` would give.
def Text.lines (text: Text): List Text := Text.linesFrom Nil Nil (Text.toList text)

-- Every remaining line of input, in order, as `IO.readLine` would give them.
-- Total: the input is read all at once.
def IO.readAllLines(): {IO} (List Text) := IO.readAll().lines

-- Prefixes, suffixes and substrings. Characters are Unicode scalar values, as
-- in `Text.length`. The main text comes first, then the prefix, suffix,
-- needle or separator, so `line.stripPrefix "L"`, `line |> Text.stripPrefix
-- "L"` and `Text.stripPrefix line "L"` all mean the same.

-- The first `n` characters of the text (all of it if it is shorter).
def Text.take (text: Text) (n: Nat): Text := Text.fromList (List.take (Text.toList text) n)

-- The text without its first `n` characters (empty if it is shorter).
def Text.drop (text: Text) (n: Nat): Text := Text.fromList (List.drop (Text.toList text) n)

-- Whether two characters are the same.
def Text.sameChar (a: Char) (b: Char): Bool := Nat.equal (Char.toNat a) (Char.toNat b)

-- The rest of the characters after the prefix `p`, if they start with it.
def Text.stripPrefixChars: List Char -> List Char -> Option (List Char)
  | Nil, ys => Some ys
  | Cons p ps, Nil => None
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.stripPrefixChars ps ys else None

def Text.startsWithChars: List Char -> List Char -> Bool
  | Nil, ys => True
  | Cons p ps, Nil => False
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.startsWithChars ps ys else False

-- `Text.stripPrefix text p` is the rest of `text` after `p`, or `None` if `text`
-- doesn't start with `p`. The empty prefix gives `Some text`.
def Text.stripPrefix (text: Text) (prefix: Text): Option Text :=
  Option.map (Text.stripPrefixChars (Text.toList prefix) (Text.toList text)) Text.fromList

-- `Text.stripSuffix text s` is `text` without its ending `s`, or `None`.
def Text.stripSuffix (text: Text) (suffix: Text): Option Text :=
  Option.map (Text.stripPrefixChars (List.reverse (Text.toList suffix)) (List.reverse (Text.toList text)))
    (chars => Text.fromList (List.reverse chars))

def Text.startsWith (text: Text) (prefix: Text): Bool :=
  Text.startsWithChars (Text.toList prefix) (Text.toList text)

def Text.endsWith (text: Text) (suffix: Text): Bool :=
  Text.startsWithChars (List.reverse (Text.toList suffix)) (List.reverse (Text.toList text))

def Text.containsChars (needle: List Char): List Char -> Bool
  | Nil => Text.startsWithChars needle Nil
  | Cons char chars => if Text.startsWithChars needle (Cons char chars) then True else Text.containsChars needle chars

-- Whether `needle` occurs in the text. The empty text occurs in every text.
def Text.contains (text: Text) (needle: Text): Bool := Text.containsChars (Text.toList needle) (Text.toList text)

-- `cur` is the current piece's characters, newest first, `acc` the finished
-- pieces, newest first, and `skip` how many more characters of a separator
-- just found are still to be passed over. `n` is the separator's length
-- less one.
def Text.splitOnLoop (sep: List Char) (n: Nat) (cur: List Char) (acc: List Text): List Char -> Nat -> List Text
  | Nil, skip => List.reverseOnto (Cons (MkText (List.reverseOnto cur Nil)) acc) Nil
  | Cons char chars, Succ skip => Text.splitOnLoop sep n cur acc chars skip
  | Cons char chars, Zero =>
    let hit := Text.startsWithChars sep (Cons char chars)
    Text.splitOnLoop sep n
      (if hit then Nil else Cons char cur)
      (if hit then Cons (MkText (List.reverseOnto cur Nil)) acc else acc)
      chars
      (if hit then n else Zero)

def Text.splitOnChars: List Char -> List Char -> List Text
  | Nil, chars => Cons (MkText chars) Nil
  | Cons first rest, chars => Text.splitOnLoop (Cons first rest) (List.length rest) Nil Nil chars Zero

-- Splits at each occurrence of the whole separator, scanning left to right
-- without overlaps: `"a--b".splitOn "-"` gives ["a", "", "b"], and
-- `Text.splitOn "aaa" "aa"` gives ["", "a"]. Always at least one piece, and
-- `Text.splitOn text s` of a text without `s` is `[text]`. An empty separator
-- doesn't split: the result is `[text]`, as in Lean's `String.splitOn`.
def Text.splitOn (text: Text) (sep: Text): List Text := Text.splitOnChars (Text.toList sep) (Text.toList text)

-- Lemmas

theorem Text.sameCharRefl (c: Char): Text.sameChar c c = True := Nat.equalRefl (Char.toNat c)

theorem Text.stripPrefixCharsAppend (t: List Char): (p: List Char) ->
    Text.stripPrefixChars p (List.append p t) = Some t
  | Nil => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.stripPrefixChars ps (List.append ps t) else None) (Text.sameCharRefl c))
      (Text.stripPrefixCharsAppend t ps)

theorem Text.stripPrefixAppend (p: Text) (t: Text): Text.stripPrefix (Text.append p t) p = Some t :=
  Eq.trans (Eq.cong (.map Text.fromList) (Text.stripPrefixCharsAppend (Text.toList t) (Text.toList p)))
    (Eq.cong Some (Text.fromToList t))

theorem Text.startsWithCharsAppend (t: List Char): (p: List Char) ->
    Text.startsWithChars p (List.append p t) = True
  | Nil => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.startsWithChars ps (List.append ps t) else False) (Text.sameCharRefl c))
      (Text.startsWithCharsAppend t ps)

theorem Text.startsWithAppend (p: Text) (t: Text): Text.startsWith (Text.append p t) p = True :=
  Text.startsWithCharsAppend (Text.toList t) (Text.toList p)

theorem Text.takeDropChars: (n: Nat) -> (cs: List Char) -> List.append (List.take cs n) (List.drop cs n) = cs
  | Zero, cs => rfl
  | Succ n, Nil => rfl
  | Succ n, Cons c cs => Eq.cong (Cons c) (Text.takeDropChars n cs)

theorem Text.takeAppendDrop (t: Text) (n: Nat): Text.append (Text.take t n) (Text.drop t n) = t :=
  Text.ext (Text.append (Text.take t n) (Text.drop t n)) t (Text.takeDropChars n (Text.toList t))

test "take and drop" := Text.take "héllo" 2 == "hé" && Text.drop "héllo" 2 == "llo"
test "take and drop past the end" := Text.take "ab" 9 == "ab" && Text.drop "ab" 9 == ""
test "stripPrefix" := Text.stripPrefix "L68" "L" == Some "68" && Text.stripPrefix "R68" "L" == None
test "stripSuffix" := Text.stripSuffix "L68" "68" == Some "L" && Text.stripSuffix "L68" "x" == None
test "startsWith and endsWith" := Text.startsWith "abc" "ab" && Text.endsWith "abc" "bc" && !(Text.startsWith "abc" "abcd")
test "contains" := Text.contains "abcd" "bc" && !(Text.contains "abcd" "ca") && Text.contains "" ""
test "splitOn" := Text.splitOn "a, b" ", " == ["a", "b"] && Text.splitOn "" "x" == [""]
test "splitOn empty separator" := Text.splitOn "abc" "" == ["abc"]
test "splitOn overlapping" := Text.splitOn "aaa" "aa" == ["", "a"]

-- `text` is the main value: `text.repeat 3` is `text` three times over; `text.repeat 0`
-- is the empty text.
def Text.repeat (text: Text) (n: Nat): Text := Text.fromList (List.concat (List.replicate n (Text.toList text)))

-- `text` is the main value: `text.chunksOf 2` cuts it into pieces of `n` characters
-- (the last one shorter if need be), as `List.chunksOf` does for lists:
-- `"abcde".chunksOf 2` is `["ab", "cd", "e"]`, and `n = 0` gives the whole
-- text as one chunk (none for an empty text).
def Text.chunksOf (text: Text) (n: Nat): List Text := List.map (List.chunksOf (Text.toList text) n) Text.fromList

test "Text.repeat" := Text.repeat "ab" 3 == "ababab" && Text.repeat "ab" 0 == "" && Text.repeat "" 4 == ""
test "Text.chunksOf" := Text.chunksOf "abcde" 2 == ["ab", "cd", "e"] && Text.chunksOf "" 2 == []
test "Text.chunksOf zero" := Text.chunksOf "abc" 0 == ["abc"]
test "Text.words" := "a  b\tc\n d ".words == ["a", "b", "c", "d"] && "".words == [] && "  ".words == [] && "ab".words == ["ab"]

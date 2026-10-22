-- Text beyond the core: the split/join and length lemmas, and `Text.lines`
-- with `IO.readAllLines`. This file was the prelude's "Lines" section and
-- the few text theorems beside it.

theorem Text.toFromList (cs: List Char): Text.toList (Text.fromList cs) = cs := rfl

theorem Text.lengthAppend (a: Text) (b: Text):
  Text.length (Text.append a b) = Text.length a + Text.length b := List.lengthAppend (Text.toList a) (Text.toList b)

-- `Text.padRight n c t` is `t` followed by enough copies of `c` to make it
-- n characters long (it is `t` itself when that is already n long or longer).
def Text.padRight (n: Nat) (c: Char) (t: Text): Text :=
  Text.fromList (List.padRight n c (Text.toList t))

theorem Text.padRightExample: Text.padRight 5 '.' "ab" = "ab..." := rfl

theorem Text.padRightLongEnough: Text.padRight 1 '.' "ab" = "ab" := rfl

def Text.less (a: Text) (b: Text): Bool := Ordering.isLess (Text.compare a b)

def Text.joinPair (s: Char): Pair (List Char) (List (List Char)) -> List Char
  | MkPair f fs => Text.joinChars s f fs

theorem Text.joinCons (s: Char) (c: Char) (f: List Char): (fs: List (List Char)) ->
    Text.joinChars s (Cons c f) fs = Cons c (Text.joinChars s f fs)
  | Nil       => rfl
  | Cons g gs => rfl

theorem Text.joinSplitCons (s: Char) (c: Char) (cs: List Char):
    (p: Pair (List Char) (List (List Char))) -> Text.joinPair s p = cs ->
    (d: Decidable (c = s)) -> Text.joinPair s (Text.splitCons s c (Decidable.toBool d) p) = Cons c cs
  | MkPair f fs, h, Yes e =>
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (x => Cons x cs) (Eq.sym e))
  | MkPair f fs, h, No r =>
    Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars (s: Char): (cs: List Char) -> Text.joinPair s (Text.splitChars s cs) = cs
  | Nil       => rfl
  | Cons c cs =>
    Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

theorem Text.charListsOfTexts: (fs: List (List Char)) -> Text.charListsOf (Text.textsOf fs) = fs
  | Nil       => rfl
  | Cons f fs => Eq.cong (Cons f) (Text.charListsOfTexts fs)

theorem Text.joinSplitTexts (s: Char): (p: Pair (List Char) (List (List Char))) ->
    Text.join s (Text.splitTexts p) = MkText (Text.joinPair s p)
  | MkPair f fs => Eq.cong (l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit (s: Char): (t: Text) -> Text.join s (Text.split s t) = t
  | MkText cs =>
    Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

-- Lines

def Char.isLineFeedCode: Nat -> Bool
  | 10 => True
  | _  => False

def Char.isCarriageReturnCode: Nat -> Bool
  | 13 => True
  | _  => False

-- A line that ended with a line feed, from its characters newest first,
-- without a carriage return just before the line feed.
def Text.endLine: List Char -> Text
  | Nil       => MkText Nil
  | Cons c cs => MkText (List.reverseOnto (if Char.isCarriageReturnCode (Char.toNat c) then cs else Cons c cs) Nil)

-- The last line, if the text doesn't end with a line feed: kept whole.
def Text.lastLine: List Char -> List Text -> List Text
  | Nil,       acc => acc
  | Cons c cs, acc => Cons (MkText (List.reverseOnto (Cons c cs) Nil)) acc

-- `line` is the current line's characters, newest first, and `acc` the
-- finished lines, newest first.
def Text.linesFrom (line: List Char) (acc: List Text): List Char -> List Text
  | Nil       => List.reverseOnto (Text.lastLine line acc) Nil
  | Cons c cs =>
    if Char.isLineFeedCode (Char.toNat c) then Text.linesFrom Nil (Cons (Text.endLine line) acc) cs
    else Text.linesFrom (Cons c line) acc cs

-- The lines of a text, without their line endings, as Rust's `str:: lines`
-- gives them. A line ends with a line feed, or a carriage return and a line
-- feed; the last line's ending is optional, so "a\nb" and "a\nb\n" both
-- give ["a", "b"], "" gives [], and "\n" gives [""]. A carriage return
-- anywhere else is kept. These are the lines `IO.readLine` would give.
def Text.lines (t: Text): List Text := Text.linesFrom Nil Nil (Text.toList t)

-- Every remaining line of input, in order, as `IO.readLine` would give them.
-- Total: the input is read all at once.
def IO.readAllLines(): {IO} (List Text) := IO.readAll().lines

-- Prefixes, suffixes and substrings. Characters are Unicode scalar values, as
-- in `Text.length`. The main text comes last, so `line |> Text.stripPrefix "L"`
-- reads well. Dot notation puts the receiver in the first parameter of type
-- `Text`, which for these functions is the prefix, separator or suffix: write
-- `t |> Text.startsWith p`, or `Text.startsWith p t`.

-- The first `n` characters of the text (all of it if it is shorter).
def Text.take (n: Nat) (t: Text): Text := Text.fromList (List.take n (Text.toList t))

-- The text without its first `n` characters (empty if it is shorter).
def Text.drop (n: Nat) (t: Text): Text := Text.fromList (List.drop n (Text.toList t))

-- Whether two characters are the same.
def Text.sameChar (a: Char) (b: Char): Bool := Nat.equal (Char.toNat a) (Char.toNat b)

-- The rest of the characters after the prefix `p`, if they start with it.
def Text.stripPrefixChars: List Char -> List Char -> Option (List Char)
  | Nil,       ys        => Some ys
  | Cons p ps, Nil       => None
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.stripPrefixChars ps ys else None

def Text.startsWithChars: List Char -> List Char -> Bool
  | Nil,       ys        => True
  | Cons p ps, Nil       => False
  | Cons p ps, Cons y ys => if Text.sameChar p y then Text.startsWithChars ps ys else False

-- `Text.stripPrefix p t` is the rest of `t` after `p`, or `None` if `t`
-- doesn't start with `p`. The empty prefix gives `Some t`.
def Text.stripPrefix (prefix: Text) (t: Text): Option Text :=
  Option.map Text.fromList (Text.stripPrefixChars (Text.toList prefix) (Text.toList t))

-- `Text.stripSuffix s t` is `t` without its ending `s`, or `None`.
def Text.stripSuffix (suffix: Text) (t: Text): Option Text :=
  Option.map (cs => Text.fromList (List.reverse cs))
    (Text.stripPrefixChars (List.reverse (Text.toList suffix)) (List.reverse (Text.toList t)))

def Text.startsWith (prefix: Text) (t: Text): Bool :=
  Text.startsWithChars (Text.toList prefix) (Text.toList t)

def Text.endsWith (suffix: Text) (t: Text): Bool :=
  Text.startsWithChars (List.reverse (Text.toList suffix)) (List.reverse (Text.toList t))

def Text.containsChars (p: List Char): List Char -> Bool
  | Nil       => Text.startsWithChars p Nil
  | Cons c cs => if Text.startsWithChars p (Cons c cs) then True else Text.containsChars p cs

-- Whether `p` occurs in the text. The empty text occurs in every text.
def Text.contains (p: Text) (t: Text): Bool := Text.containsChars (Text.toList p) (Text.toList t)

-- `cur` is the current piece's characters, newest first, `acc` the finished
-- pieces, newest first, and `skip` how many more characters of a separator
-- just found are still to be passed over. `n` is the separator's length
-- less one.
def Text.splitOnLoop (sep: List Char) (n: Nat) (cur: List Char) (acc: List Text): List Char -> Nat -> List Text
  | Nil,       skip      => List.reverseOnto (Cons (MkText (List.reverseOnto cur Nil)) acc) Nil
  | Cons c cs, Succ skip => Text.splitOnLoop sep n cur acc cs skip
  | Cons c cs, Zero      =>
    let hit := Text.startsWithChars sep (Cons c cs)
    Text.splitOnLoop sep n
      (if hit then Nil else Cons c cur)
      (if hit then Cons (MkText (List.reverseOnto cur Nil)) acc else acc)
      cs
      (if hit then n else Zero)

def Text.splitOnChars: List Char -> List Char -> List Text
  | Nil,        cs => Cons (MkText cs) Nil
  | Cons s ss,  cs => Text.splitOnLoop (Cons s ss) (List.length ss) Nil Nil cs Zero

-- Splits at each occurrence of the whole separator, scanning left to right
-- without overlaps: `"a--b".splitOn "-"` gives ["a", "", "b"], and
-- `Text.splitOn "aa" "aaa"` gives ["", "a"]. Always at least one piece, and
-- `Text.splitOn s t` of a text without `s` is `[t]`. An empty separator
-- doesn't split: the result is `[t]`, as in Lean's `String.splitOn`.
def Text.splitOn (sep: Text) (t: Text): List Text := Text.splitOnChars (Text.toList sep) (Text.toList t)

-- Lemmas

theorem Text.sameCharRefl (c: Char): Text.sameChar c c = True := Nat.equalRefl (Char.toNat c)

theorem Text.stripPrefixCharsAppend (t: List Char): (p: List Char) ->
    Text.stripPrefixChars p (List.append p t) = Some t
  | Nil       => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.stripPrefixChars ps (List.append ps t) else None) (Text.sameCharRefl c))
      (Text.stripPrefixCharsAppend t ps)

theorem Text.stripPrefixAppend (p: Text) (t: Text): Text.stripPrefix p (Text.append p t) = Some t :=
  Eq.trans (Eq.cong (Option.map Text.fromList) (Text.stripPrefixCharsAppend (Text.toList t) (Text.toList p)))
    (Eq.cong Some (Text.fromToList t))

theorem Text.startsWithCharsAppend (t: List Char): (p: List Char) ->
    Text.startsWithChars p (List.append p t) = True
  | Nil       => rfl
  | Cons c ps =>
    Eq.trans (Eq.cong (b => if b then Text.startsWithChars ps (List.append ps t) else False) (Text.sameCharRefl c))
      (Text.startsWithCharsAppend t ps)

theorem Text.startsWithAppend (p: Text) (t: Text): Text.startsWith p (Text.append p t) = True :=
  Text.startsWithCharsAppend (Text.toList t) (Text.toList p)

theorem Text.takeDropChars: (n: Nat) -> (cs: List Char) -> List.append (List.take n cs) (List.drop n cs) = cs
  | Zero,   cs        => rfl
  | Succ n, Nil       => rfl
  | Succ n, Cons c cs => Eq.cong (Cons c) (Text.takeDropChars n cs)

theorem Text.takeAppendDrop (n: Nat) (t: Text): Text.append (Text.take n t) (Text.drop n t) = t :=
  Text.ext (Text.append (Text.take n t) (Text.drop n t)) t (Text.takeDropChars n (Text.toList t))

test "take and drop" := Text.take 2 "héllo" == "hé" && Text.drop 2 "héllo" == "llo"
test "take and drop past the end" := Text.take 9 "ab" == "ab" && Text.drop 9 "ab" == ""
test "stripPrefix" := Text.stripPrefix "L" "L68" == Some "68" && Text.stripPrefix "L" "R68" == None
test "stripSuffix" := Text.stripSuffix "68" "L68" == Some "L" && Text.stripSuffix "x" "L68" == None
test "startsWith and endsWith" := Text.startsWith "ab" "abc" && Text.endsWith "bc" "abc" && !(Text.startsWith "abcd" "abc")
test "contains" := Text.contains "bc" "abcd" && !(Text.contains "ca" "abcd") && Text.contains "" ""
test "splitOn" := Text.splitOn ", " "a, b" == ["a", "b"] && Text.splitOn "x" "" == [""]
test "splitOn empty separator" := Text.splitOn "" "abc" == ["abc"]
test "splitOn overlapping" := Text.splitOn "aa" "aaa" == ["", "a"]

-- `t` is the main value: `t.repeat 3` is `t` three times over; `t.repeat 0`
-- is the empty text.
def Text.repeat (t: Text) (n: Nat): Text := Text.fromList (List.concat (List.replicate n (Text.toList t)))

-- `t` is the main value: `t.chunksOf 2` cuts it into pieces of `n` characters
-- (the last one shorter if need be), as `List.chunksOf` does for lists:
-- `"abcde".chunksOf 2` is `["ab", "cd", "e"]`, and `n = 0` gives the whole
-- text as one chunk (none for an empty text).
def Text.chunksOf (t: Text) (n: Nat): List Text := List.map Text.fromList (List.chunksOf (Text.toList t) n)

test "Text.repeat" := Text.repeat "ab" 3 == "ababab" && Text.repeat "ab" 0 == "" && Text.repeat "" 4 == ""
test "Text.chunksOf" := Text.chunksOf "abcde" 2 == ["ab", "cd", "e"] && Text.chunksOf "" 2 == []
test "List.distinct texts" := ["a", "b", "a"].distinct == ["a", "b"]
test "Text.chunksOf zero" := Text.chunksOf "abc" 0 == ["abc"]
test "Text.words" := "a  b\tc\n d ".words == ["a", "b", "c", "d"] && "".words == [] && "  ".words == [] && "ab".words == ["ab"]

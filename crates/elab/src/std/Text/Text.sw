-- Text beyond the core: the split/join and length lemmas, the `.toText`
-- conversions, and `Text.lines` with `IO.readAllLines`. This file was the
-- prelude's "Lines" section and the few text theorems beside it.

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

-- Itself: so `"${t}"` works when `t` is already text.
def Text.toText (t: Text): Text := t

-- The character on its own: `'a'.toText` is `"a"`.
def Char.toText (c: Char): Text := MkText [c]

-- `"True"` or `"False"`, as the constructors are written.
def Bool.toText: Bool -> Text
  | True  => "True"
  | False => "False"

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
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (\x => Cons x cs) (Eq.sym e))
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
  | MkPair f fs => Eq.cong (\l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

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
def IO.readAllLines(): {IO} (List Text) := (IO.readAll()).lines

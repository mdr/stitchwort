--| Text beyond the core: the split/join and length lemmas, and `Text.lines`
--| with `IO.readAllLines`.
-- This file was the prelude's "Lines" section and the few text theorems
-- beside it.

theorem Text.toFromList ∀ (cs: List Char): Text.toList (Text.fromList cs) = cs := rfl

--| The character at index `index`, counting from 0, or `None` past the end: as
--| [`List.get`] on [`Text.toList`] ([`Text.getToList`]).
def Text.get (text: Text) (index: Nat): Option Char := text.toList.get index

theorem Text.getToList ∀ (text: Text) (i: Nat): Text.get text i = List.get text.toList i := rfl

--| How many characters satisfy `p`: as [`List.count`] on [`Text.toList`]
--| ([`Text.countToList`]).
def Text.count (text: Text) (p: Char → Bool): Nat := text.toList.count p

theorem Text.countToList ∀ (text: Text) (p: Char → Bool): Text.count text p = List.count text.toList p := rfl

--| Whether some character satisfies `p`: as [`List.any`] on [`Text.toList`]
--| ([`Text.anyToList`]).
def Text.any (text: Text) (p: Char → Bool): Bool := text.toList.any p

theorem Text.anyToList ∀ (text: Text) (p: Char → Bool): Text.any text p = List.any text.toList p := rfl

--| Whether every character satisfies `p`: as [`List.all`] on [`Text.toList`]
--| ([`Text.allToList`]).
def Text.all (text: Text) (p: Char → Bool): Bool := text.toList.all p

theorem Text.allToList ∀ (text: Text) (p: Char → Bool): Text.all text p = List.all text.toList p := rfl

test "Text.get" := Text.get "abc" 0 == Some 'a' ∧ Text.get "abc" 2 == Some 'c' ∧ Text.get "abc" 3 == None

test "Text.count" := Text.count "banana" (== 'a') == 3 ∧ Text.count "abc" (== 'z') == 0 ∧ Text.count "" (== 'a') == 0

test "Text.any and Text.all" :=
  Text.any "abc" (== 'b') ∧ ¬(Text.any "abc" (== 'z')) ∧ Text.all "aaa" (== 'a') ∧ ¬(Text.all "aba" (== 'a'))

theorem Text.lengthAppend ∀ (a b: Text): Text.length (Text.append a b) = Text.length a + Text.length b :=
  List.lengthAppend (Text.toList a) (Text.toList b)

--| The text made `width` characters long with copies of `char` after it: `Text.padRight "ab" 5 '.'` is `"ab..."`.
--| It is `text` itself when that is already `width` long or longer.
def Text.padRight (text: Text) (width: Nat) (char: Char): Text := text.toList.padRight width char |> Text.fromList

theorem Text.padRightExample: Text.padRight "ab" 5 '.' = "ab..." := rfl

theorem Text.padRightLongEnough: Text.padRight "ab" 1 '.' = "ab" := rfl

--| The text made `width` characters long with copies of `char` before it: `Text.padLeft "7" 2 '0'` is `"07"`.
--| It is `text` itself when that is already `width` long or longer.
def Text.padLeft (text: Text) (width: Nat) (char: Char): Text := text.toList.padLeft width char |> Text.fromList

theorem Text.padLeftExample: Text.padLeft "7" 2 '0' = "07" := rfl

theorem Text.padLeftLongEnough: Text.padLeft "123" 2 '0' = "123" := rfl

--| Whether `a` comes before `b`, lexicographically by scalar value.
def Text.less (a b: Text): Bool := Ordering.isLess (Text.compare a b)

--| A first field and the fields after it, joined with `separator` between each two.
def Text.joinPair (separator: Char): (state: Pair (List Char) (List (List Char))) → List Char
  | MkPair field fields => Text.joinChars separator field fields

theorem Text.joinCons ∀ (s c: Char) (f: List Char) (fs: List (List Char)):
    Text.joinChars s [c, ..f] fs = [c, ..Text.joinChars s f fs] :=
  match fs with
    | [] => rfl
    | [g, ..gs] => rfl

theorem Text.joinSplitCons ∀ (s c: Char) (cs: List Char):
    ∀ (p: Pair (List Char) (List (List Char))) => Text.joinPair s p = cs
      → ∀ (d: Decidable (c = s)) => Text.joinPair s (Text.splitCons s c (Decidable.holds d) p) = [c, ..cs]
  | MkPair f fs, h, { holds = True, sound = e, complete = _ } =>
    Eq.trans (Eq.cong (Cons s) h) (Eq.cong (x => [x, ..cs]) (Eq.sym (e rfl)))
  | MkPair f fs, h, { holds = False, sound = _, complete = _ } => Eq.trans (Text.joinCons s c f fs) (Eq.cong (Cons c) h)

theorem Text.joinSplitChars ∀ (s: Char) (cs: List Char): Text.joinPair s (Text.splitChars s cs) = cs := match cs with
  | [] => rfl
  | [c, ..cs] => Text.joinSplitCons s c cs (Text.splitChars s cs) (Text.joinSplitChars s cs) (Char.decEq c s)

theorem Text.charListsOfTexts ∀ (fs: List (List Char)): Text.charListsOf (Text.textsOf fs) = fs := match fs with
  | [] => rfl
  | [f, ..fs] => Eq.cong (Cons f) (Text.charListsOfTexts fs)

theorem Text.joinSplitTexts ∀ (s: Char) (p: Pair (List Char) (List (List Char))):
    Text.join (Text.splitTexts p) s = MkText (Text.joinPair s p) :=
  match p with | MkPair f fs => Eq.cong (l => MkText (Text.joinChars s f l)) (Text.charListsOfTexts fs)

theorem Text.joinSplit ∀ (t: Text) (s: Char): Text.join (Text.split t s) s = t := match t with
  | MkText cs => Eq.trans (Text.joinSplitTexts s (Text.splitChars s cs)) (Eq.cong MkText (Text.joinSplitChars s cs))

-- Lines

--| Whether a code is the line feed, 10.
def Char.isLineFeedCode: (code: Nat) → Bool := matches | 10

--| Whether a code is the carriage return, 13.
def Char.isCarriageReturnCode: (code: Nat) → Bool := matches | 13

--| A line that ended with a line feed, from its characters newest first,
--| without a carriage return just before the line feed.
def Text.endLine: (chars: List Char) → Text
  | [] => MkText []
  | [char, ..chars] =>
    MkText (List.reverseOnto (if Char.isCarriageReturnCode (Char.toNat char) then chars else [char, ..chars]) [])

--| The last line, if the text doesn't end with a line feed: kept whole.
def Text.lastLine: (line: List Char) → (lines: List Text) → List Text
  | [], acc => acc
  | [c, ..cs], acc => [MkText (List.reverseOnto [c, ..cs] []), ..acc]

--| The lines of the characters, after the current line's characters
--| (`line`, newest first) and the finished lines (`acc`, newest first).
@[tailrec]
def Text.linesFrom (line: List Char) (acc: List Text): (chars: List Char) → List Text
  | [] => List.reverseOnto (Text.lastLine line acc) []
  | [char, ..chars] =>
    if Char.isLineFeedCode (Char.toNat char) then Text.linesFrom [] [Text.endLine line, ..acc] chars
    else Text.linesFrom [char, ..line] acc chars

--| The lines of a text, without their line endings, as Rust's `str:: lines`
--| gives them. A line ends with a line feed, or a carriage return and a line
--| feed; the last line's ending is optional, so "a\nb" and "a\nb\n" both
--| give ["a", "b"], "" gives [], and "\n" gives [""]. A carriage return
--| anywhere else is kept. These are the lines `IO.readLine` would give.
def Text.lines (text: Text): List Text := Text.linesFrom [] [] (Text.toList text)

--| Every remaining line of input, in order, as `IO.readLine` would give them.
--| Total: the input is read all at once.
def IO.readAllLines(): {IO} List Text := IO.readAll().lines

-- What `Text.lines` does, as lemmas. The lines of a chunk that ends with a
-- line feed don't depend on what follows it, and a line with no carriage
-- return in it is its characters; a carriage return is where the lines stop
-- being the characters: "a\r\n" and "a\n" both give "a".

--| A carriage return before a line feed is part of the line ending, not of the
--| line: "a\r\nb\r" has the lines "a" and "b\r" (nothing follows the last).
theorem Text.linesCarriageReturnExample: "a\r\nb\r".lines = ["a", "b\r"] := rfl

--| A line feed after a final line feed is an empty line; a carriage return
--| alone, after one, is a line of its own.
theorem Text.linesFinalBreaksExample: "a\n\r\n".lines = ["a", ""] ∧ "a\n\r".lines = ["a", "\r"] := Both rfl rfl

--| `Char.isLineFeedCode` holds of the code 10 only.
theorem Char.lineFeedCodeIs ∀ (code: Nat) (h: Char.isLineFeedCode code = True): code = 10 := match code with | 10 => rfl

--| A space or a tab is neither a line feed nor a carriage return.
theorem Text.spaceTabPlain ∀ (char: Char)
    (h: (char == ' ' ∨ char == '\t') = True):
    Char.isLineFeedCode (Char.toNat char) = False ∧ Char.isCarriageReturnCode (Char.toNat char) = False :=
  match h with
    | Inl left => rewrite left.read in Both rfl rfl
    | Inr right => rewrite right.read in Both rfl rfl

--| `Text.linesFrom` keeps its finished lines apart from the line it is on:
--| the finished lines (`acc`, newest first) come first, in order.
theorem Text.linesFromAcc ∀ (chars line: List Char) (acc: List Text):
    Text.linesFrom line acc chars = List.append (List.reverseOnto acc []) (Text.linesFrom line [] chars) :=
  match chars, line with
    | [], [] => rewrite List.appendNil (List.reverseOnto acc []) in rfl
    | [], [c, ..cs] => List.reverseOntoAppend acc [MkText (List.reverseOnto [c, ..cs] [])]
    | [char, ..chars], line =>
      match Char.isLineFeedCode (Char.toNat char) with
        | True =>
          rewrite Text.linesFromAcc chars [] [Text.endLine line, ..acc],
              Text.linesFromAcc chars [] [Text.endLine line],
              List.reverseOntoAppend acc [Text.endLine line],
              List.appendAssoc (List.reverseOnto acc []) [Text.endLine line] (Text.linesFrom [] [] chars) in
            rfl
        | False => Text.linesFromAcc chars [char, ..line] acc

theorem Text.linesFromAppend ∀ (front line: List Char) (acc: List Text) (rest: List Char):
    Text.linesFrom line acc (front ++ ['\n'] ++ rest)
      = Text.linesFrom line acc (front ++ ['\n']) ++ Text.linesFrom [] [] rest :=
  match front with
    | [] => Text.linesFromAcc rest [] [Text.endLine line, ..acc]
    | [char, ..chars] =>
      match Char.isLineFeedCode (Char.toNat char) with
        | True => Text.linesFromAppend chars [] [Text.endLine line, ..acc] rest
        | False => Text.linesFromAppend chars [char, ..line] acc rest

--| The lines of a text are the lines of its part up to a line feed, then
--| the lines of the rest: a line feed ends a line whatever came before it.
--| The split is exact, with nothing assumed of either part.
theorem Text.linesAppend ∀ (front rest: List Char):
    Text.lines (MkText (front ++ ['\n'] ++ rest)) = Text.lines (MkText (front ++ ['\n'])) ++ Text.lines (MkText rest) :=
  Text.linesFromAppend front [] [] rest

theorem Text.linesFromLine: ∀ (front: List Char) => List.All (c => Char.isLineFeedCode (Char.toNat c) = False) front
      → ∀ (line: List Char) (acc: List Text) (rest: List Char) => Text.linesFrom line acc (front ++ ['\n'] ++ rest)
        = Text.linesFrom [] [Text.endLine (List.reverseOnto front line), ..acc] rest
  | [], none, line, acc, rest => rfl
  | [char, ..chars], Both notFeed others, line, acc, rest =>
    rewrite notFeed in Text.linesFromLine chars others [char, ..line] acc rest

--| The first line of a text with a line feed: the characters before the
--| first line feed (less a carriage return just before it, as
--| [`Text.endLine`] takes it off), then the lines of the rest.
theorem Text.linesLine ∀ (front rest: List Char)
    (noFeed: List.All (c => Char.isLineFeedCode (Char.toNat c) = False) front):
    Text.lines (MkText (front ++ ['\n'] ++ rest)) = [Text.endLine (List.reverse front), ..Text.lines (MkText rest)] :=
  Eq.trans (Text.linesFromLine front noFeed [] [] rest) (Text.linesFromAcc rest [] [Text.endLine (List.reverse front)])

theorem Text.endLinePlain ∀ (middle: List Char)
    (plain: List.All
      (c => Char.isLineFeedCode (Char.toNat c) = False ∧ Char.isCarriageReturnCode (Char.toNat c) = False)
      middle):
    Text.endLine (List.reverseOnto middle []) = MkText middle :=
  match e: List.reverseOnto middle [] with
    | [] => Eq.cong MkText (Eq.sym (Eq.trans (Eq.sym (List.reverseOntoTwice middle [])) (rewrite e in rfl)))
    | [char, ..chars] =>
      let member: char ∈ List.reverseOnto middle [] := rewrite e in Inl rfl
      let inMiddle: char ∈ middle :=
        Or.elim ((List.memReverseOnto char middle []).forward member) (found => found) (found => Void.exfalso found)
      match List.allMem _ char middle plain inMiddle with
        | Both notFeed notReturn =>
          rewrite notReturn in
            Eq.cong MkText
              (Eq.trans (Eq.cong (l => List.reverseOnto l []) (Eq.sym e)) (List.reverseOntoTwice middle []))

--| A line of plain characters (no line feed, no carriage return) ended by a
--| line feed is exactly those characters: it is the text's first line, and
--| the lines of the rest follow.
theorem Text.linesPlainLine ∀ (middle rest: List Char)
    (plain: List.All
      (c => Char.isLineFeedCode (Char.toNat c) = False ∧ Char.isCarriageReturnCode (Char.toNat c) = False)
      middle):
    Text.lines (MkText (middle ++ ['\n'] ++ rest)) = [MkText middle, ..Text.lines (MkText rest)] :=
  Eq.trans
    (Text.linesLine middle rest (List.allImplies _ _ (c both => And.left both) middle plain))
    (Eq.cong (l => [l, ..Text.lines (MkText rest)]) (Text.endLinePlain middle plain))

--| The same, ended by a carriage return and a line feed: the carriage return
--| is not part of the line.
theorem Text.linesPlainLineReturn ∀ (middle rest: List Char)
    (plain: List.All
      (c => Char.isLineFeedCode (Char.toNat c) = False ∧ Char.isCarriageReturnCode (Char.toNat c) = False)
      middle):
    Text.lines (MkText (middle ++ ['\r', '\n'] ++ rest)) = [MkText middle, ..Text.lines (MkText rest)] :=
  let noFeed: List.All (c => Char.isLineFeedCode (Char.toNat c) = False) (middle ++ ['\r']) :=
    List.allAppend _ middle ['\r'] (List.allImplies _ _ (c both => And.left both) middle plain) (Both rfl ())
  let endsPlain: Text.endLine (List.reverse (middle ++ ['\r'])) = MkText middle :=
    Eq.trans
      (Eq.cong Text.endLine (List.reverseAppend middle ['\r']))
      (Eq.cong MkText (List.reverseOntoTwice middle []))
  Eq.trans
    (Eq.cong (l => Text.lines (MkText l)) (Eq.sym (List.appendAssoc middle ['\r'] ['\n', ..rest])))
    (Eq.trans
      (Text.linesLine (middle ++ ['\r']) rest noFeed)
      (Eq.cong (e => [e, ..Text.lines (MkText rest)]) endsPlain))

theorem Text.linesFromNoFeed: ∀ (chars: List Char) => List.All (c => Char.isLineFeedCode (Char.toNat c) = False) chars
      → ∀ (line: List Char) (acc: List Text) => Text.linesFrom line acc chars
        = List.reverseOnto (Text.lastLine (List.reverseOnto chars line) acc) []
  | [], none, line, acc => rfl
  | [char, ..chars], Both notFeed others, line, acc =>
    rewrite notFeed in Text.linesFromNoFeed chars others [char, ..line] acc

--| A text with no line feed that isn't empty is one line, whole, carriage
--| returns and all (the empty text has no lines).
theorem Text.linesNoFeed ∀ (first: Char) (chars: List Char)
    (noFeed: List.All (c => Char.isLineFeedCode (Char.toNat c) = False) [first, ..chars]):
    Text.lines (MkText [first, ..chars]) = [MkText [first, ..chars]] :=
  let flowed := Text.linesFromNoFeed [first, ..chars] noFeed [] []
  let member: first ∈ List.reverseOnto [first, ..chars] [] :=
    (List.memReverseOnto first [first, ..chars] []).backward (Inl (Inl rfl))
  match e: List.reverseOnto [first, ..chars] [] with
    | [last, ..rest] =>
      Eq.trans flowed
        (Eq.cong
          (l => [MkText l])
          (Eq.trans (Eq.cong (l => List.reverseOnto l []) (Eq.sym e)) (List.reverseOntoTwice chars [first])))

--| The characters of lines, each followed by a line feed.
def Text.unlinesChars: (lines: List Text) → List Char
  | [] => []
  | [line, ..lines] => Text.toList line ++ ['\n'] ++ Text.unlinesChars lines

theorem Text.unlinesAppend ∀ (xs ys: List Text):
    Text.unlinesChars (xs ++ ys) = Text.unlinesChars xs ++ Text.unlinesChars ys :=
  match xs with
    | [] => rfl
    | [x, ..xs] =>
      Eq.trans
        (Eq.cong (l => Text.toList x ++ ['\n', ..l]) (Text.unlinesAppend xs ys))
        (Eq.sym (List.appendAssoc (Text.toList x) ['\n', ..Text.unlinesChars xs] (Text.unlinesChars ys)))

theorem Text.endLineNoReturn ∀ (line: List Char)
    (none: List.All (c => Char.isCarriageReturnCode (Char.toNat c) = False) line):
    Text.endLine line = MkText (List.reverseOnto line []) :=
  match line, none with
    | [], none => rfl
    | [char, ..chars], Both notReturn others => rewrite notReturn in rfl

theorem Text.unlinesFrom: ∀ (front: List Char) => List.All (c => Char.isCarriageReturnCode (Char.toNat c) = False) front
      → ∀ (line: List Char) => List.All (c => Char.isCarriageReturnCode (Char.toNat c) = False) line
        → Text.unlinesChars (Text.linesFrom line [] (front ++ ['\n'])) = List.reverseOnto line [] ++ front ++ ['\n']
  | [], none, line, noReturn => rewrite Text.endLineNoReturn line noReturn in rfl
  | [char, ..chars], Both notReturn others, line, noReturn =>
    match c: Char.isLineFeedCode (Char.toNat char) with
      | True =>
        let isFeed: char = '\n' := Char.ext char '\n' (Char.lineFeedCodeIs _ c)
        rewrite isFeed,
            Text.linesFromAcc (chars ++ ['\n']) [] [Text.endLine line],
            Text.unlinesAppend [Text.endLine line] (Text.linesFrom [] [] (chars ++ ['\n'])),
            Text.unlinesFrom chars others [] (),
            Text.endLineNoReturn line noReturn in
          List.appendAssoc (List.reverseOnto line []) ['\n'] (chars ++ ['\n'])
      | False =>
        rewrite Text.unlinesFrom chars others [char, ..line] (Both notReturn noReturn),
            List.reverseOntoAppend line [char] in
          List.appendAssoc (List.reverseOnto line []) [char] (chars ++ ['\n'])

--| A text with no carriage return that ends with a line feed is its lines,
--| each followed by a line feed: the lines lose nothing.
theorem Text.unlinesLines ∀ (front: List Char)
    (noReturn: List.All (c => Char.isCarriageReturnCode (Char.toNat c) = False) front):
    Text.unlinesChars (Text.lines (MkText (front ++ ['\n']))) = front ++ ['\n'] :=
  Text.unlinesFrom front noReturn [] ()

theorem Text.linesFromUnterminated ∀ (last: Char)
    (notFeed: Char.isLineFeedCode (Char.toNat last) = False)
    (notReturn: Char.isCarriageReturnCode (Char.toNat last) = False)
    (front line: List Char) (acc: List Text):
    Text.linesFrom line acc (front ++ [last]) = Text.linesFrom line acc (front ++ [last, '\n']) :=
  match front with
    | [] => rewrite notFeed, notReturn in rfl
    | [char, ..chars] =>
      match Char.isLineFeedCode (Char.toNat char) with
        | True => Text.linesFromUnterminated last notFeed notReturn chars [] [Text.endLine line, ..acc]
        | False => Text.linesFromUnterminated last notFeed notReturn chars [char, ..line] acc

--| A last line without its line feed gives the same lines as with one, if
--| its last character isn't a carriage return (one there is dropped before
--| a line feed, but kept when nothing follows).
theorem Text.linesUnterminated ∀ (front: List Char) (last: Char)
    (notFeed: Char.isLineFeedCode (Char.toNat last) = False)
    (notReturn: Char.isCarriageReturnCode (Char.toNat last) = False):
    Text.lines (MkText (front ++ [last])) = Text.lines (MkText (front ++ [last, '\n'])) :=
  Text.linesFromUnterminated last notFeed notReturn front [] []

-- Prefixes, suffixes and substrings. Characters are Unicode scalar values, as
-- in `Text.length`. The main text comes first, then the prefix, suffix,
-- needle or separator, so `line.stripPrefix "L"`, `line |> Text.stripPrefix
-- "L"` and `Text.stripPrefix line "L"` all mean the same.

--| The first `count` characters of the text (all of it if it is shorter); with `Text.drop`, the whole text ([`Text.takeAppendDrop`]).
def Text.take (text: Text) (count: Nat): Text := text.toList.take count |> Text.fromList

--| The text without its first `count` characters (empty if it is shorter).
def Text.drop (text: Text) (count: Nat): Text := text.toList.drop count |> Text.fromList

--| Whether two characters are the same.
def Text.sameChar (a b: Char): Bool := Nat.equal (Char.toNat a) (Char.toNat b)

--| The rest of the characters after the prefix `p`, if they start with it.
@[tailrec]
def Text.stripPrefixChars: (prefix: List Char) → (chars: List Char) → Option (List Char)
  | [], ys => Some ys
  | [p, ..ps], [] => None
  | [p, ..ps], [y, ..ys] => if Text.sameChar p y then Text.stripPrefixChars ps ys else None

--| Whether the second list of characters starts with the first.
@[tailrec]
def Text.startsWithChars: (prefix: List Char) → (chars: List Char) → Bool
  | [], ys => True
  | [p, ..ps], [] => False
  | [p, ..ps], [y, ..ys] => if Text.sameChar p y then Text.startsWithChars ps ys else False

--| The rest of `text` after `prefix`, or `None` if `text` doesn't start with it
--| ([`Text.stripPrefixAppend`], [`Text.stripPrefixSome`]). The empty prefix gives `Some text`.
def Text.stripPrefix (text prefix: Text): Option Text :=
  Text.stripPrefixChars prefix.toList text.toList |> .map Text.fromList

--| The text without its ending `suffix`, or `None` if it doesn't end with it
--| ([`Text.stripSuffixSome`]).
def Text.stripSuffix (text suffix: Text): Option Text :=
  Text.stripPrefixChars suffix.toList.reverse text.toList.reverse |> .map (chars => chars.reverse |> Text.fromList)

--| Whether `text` starts with `prefix` ([`Text.startsWithAppend`]).
def Text.startsWith (text prefix: Text): Bool := Text.startsWithChars prefix.toList text.toList

--| Whether `text` ends with `suffix`.
def Text.endsWith (text suffix: Text): Bool := Text.startsWithChars suffix.toList.reverse text.toList.reverse

--| Whether `needle` occurs in the list of characters.
@[tailrec]
def Text.containsChars (needle: List Char): (chars: List Char) → Bool
  | [] => Text.startsWithChars needle []
  | [char, ..chars] => if Text.startsWithChars needle [char, ..chars] then True else Text.containsChars needle chars

--| Whether `needle` occurs in the text. The empty text occurs in every text.
def Text.contains (text needle: Text): Bool := Text.containsChars needle.toList text.toList

--| The loop of `Text.splitOn`, reading the characters. `cur` is the current
--| piece's characters, newest first, `acc` the finished pieces, newest first,
--| and `skip` how many more characters of a separator just found are still to
--| be passed over. `n` is the separator's length less one.
@[tailrec]
def Text.splitOnLoop (sep: List Char) (n: Nat) (cur: List Char) (acc: List Text):
    (chars: List Char) → (skip: Nat) → List Text
  | [], skip => List.reverseOnto [MkText (List.reverseOnto cur []), ..acc] []
  | [char, ..chars], Succ skip => Text.splitOnLoop sep n cur acc chars skip
  | [char, ..chars], Zero =>
    let hit := Text.startsWithChars sep [char, ..chars]
    Text.splitOnLoop sep n
      (if hit then [] else [char, ..cur])
      (if hit then [MkText (List.reverseOnto cur []), ..acc] else acc)
      chars
      (if hit then n else Zero)

--| The characters split at each occurrence of the separator, as `Text.splitOn` does it.
def Text.splitOnChars: (sep: List Char) → (chars: List Char) → List Text
  | [], chars => [MkText chars]
  | [first, ..rest], chars => Text.splitOnLoop [first, ..rest] (List.length rest) [] [] chars Zero

--| The pieces between occurrences of the whole separator: `"a--b".splitOn "-"` gives ["a", "", "b"].
--| It scans left to right without overlaps, so
--| `Text.splitOn "aaa" "aa"` gives ["", "a"]. Always at least one piece, and
--| `Text.splitOn text s` of a text without `s` is `[text]`. An empty separator
--| doesn't split: the result is `[text]`, as in Lean's `String.splitOn`.
def Text.splitOn (text sep: Text): List Text := Text.splitOnChars sep.toList text.toList

-- Lemmas

theorem Text.sameCharRefl ∀ (c: Char): Text.sameChar c c = True := Nat.equalRefl (Char.toNat c)

theorem Text.stripPrefixCharsAppend ∀ (t p: List Char): Text.stripPrefixChars p (List.append p t) = Some t :=
  match p with
    | [] => rfl
    | [c, ..ps] =>
      Eq.trans
        (Eq.cong (b => if b then Text.stripPrefixChars ps (List.append ps t) else None) (Text.sameCharRefl c))
        (Text.stripPrefixCharsAppend t ps)

theorem Text.stripPrefixAppend ∀ (p t: Text): Text.stripPrefix (Text.append p t) p = Some t :=
  Eq.trans
    (Eq.cong (.map Text.fromList) (Text.stripPrefixCharsAppend (Text.toList t) (Text.toList p)))
    (Eq.cong Some (Text.fromToList t))

--| Comparing characters with `Text.sameChar` is comparing them with `==`.
--| Use it to read `Text.stripPrefixChars` and `Text.startsWithChars`, which
--| compare by code, as if they used `==`.
theorem Text.sameCharEq ∀ (c d: Char): Text.sameChar c d = (c == d) := match same: Text.sameChar c d with
  | True => rfl
  | False =>
    match equal: c == d with
      | False => rfl

--| The direction of [`Text.stripPrefixCharsSome`] that reads a result: when
--| stripping `p` from `ys` leaves `rest`, `ys` is `p` followed by `rest`.
theorem Text.stripPrefixCharsForward ∀ (p ys: List Char) [rest: List Char]
    (h: Text.stripPrefixChars p ys = Some rest):
    ys = List.append p rest :=
  match p, ys with
    | [], ys => Option.someInjective h
    | [c, ..ps], [y, ..ys] =>
      match same: Text.sameChar c y with
        | True => rewrite Eq.sym (Char.ext c y same.read) in Eq.cong (Cons c) (Text.stripPrefixCharsForward ps ys h)

--| The characters after the prefix `p` are `rest` exactly when the list is
--| `p` followed by `rest`: `Text.stripPrefixChars p ys = Some rest ↔ ys = p ++ rest`.
theorem Text.stripPrefixCharsSome ∀ (p ys rest: List Char):
    Text.stripPrefixChars p ys = Some rest ↔ ys = List.append p rest :=
  { forward = Text.stripPrefixCharsForward p ys, backward = e => rewrite e in Text.stripPrefixCharsAppend rest p }

--| Texts are equal exactly when their character lists are: `Text.fromList a == Text.fromList b`
--| is `a == b`. Use it to move a `Bool` equation between a text and its characters.
theorem Text.fromListEq [a b: List Char]: (Text.fromList a == Text.fromList b) = (a == b) := match same: a == b with
  | True => rfl
  | False =>
    match equal: Text.fromList a == Text.fromList b with
      | False => rfl

--| `text` after `prefix` is `rest` exactly when `text` is `prefix` followed by
--| `rest`: `text.stripPrefix prefix = Some rest ↔ text = Text.append prefix rest`.
--| Use it to turn a `stripPrefix` result into an equation about the text, or the
--| reverse. `Text.stripPrefixAppend` is its `backward` direction at
--| `text = Text.append prefix rest`.
--| Example: `(Text.stripPrefixSome "L68" "L" "68").backward rfl` proves
--| `"L68".stripPrefix "L" = Some "68"`.
theorem Text.stripPrefixSome ∀ (text prefix rest: Text):
    Text.stripPrefix text prefix = Some rest ↔ text = Text.append prefix rest :=
  {
    forward = h =>
      match found: Text.stripPrefixChars (Text.toList prefix) (Text.toList text) with
        | Some chars =>
          Text.ext text
            (Text.append prefix rest)
            (rewrite Text.stripPrefixCharsForward _ _ found, Eq.sym (Option.someInjective h) in rfl),
    backward = e => rewrite e in Text.stripPrefixAppend prefix rest
  }

--| `text` without its ending `suffix` is `rest` exactly when `text` is `rest`
--| followed by `suffix`: `text.stripSuffix suffix = Some rest ↔ text = Text.append rest suffix`.
--| Use it to turn a `stripSuffix` result into an equation about the text, or the
--| reverse. Example: `(Text.stripSuffixSome "L68" "68" "L").backward rfl` proves
--| `"L68".stripSuffix "68" = Some "L"`.
theorem Text.stripSuffixSome ∀ (text suffix rest: Text):
    Text.stripSuffix text suffix = Some rest ↔ text = Text.append rest suffix :=
  {
    forward = h =>
      match found: Text.stripPrefixChars (List.reverse (Text.toList suffix)) (List.reverse (Text.toList text)) with
        | Some chars =>
          Text.ext text
            (Text.append rest suffix)
            (Eq.trans
              (Eq.sym (List.reverseReverse (Text.toList text)))
              (rewrite Text.stripPrefixCharsForward _ _ found,
                  Eq.sym (Option.someInjective h),
                  List.reverseAppend (List.reverse (Text.toList suffix)) chars,
                  List.reverseReverse (Text.toList suffix) in
                rfl)),
    backward = e =>
      rewrite e,
          List.reverseAppend (Text.toList rest) (Text.toList suffix),
          Text.stripPrefixCharsAppend (List.reverse (Text.toList rest)) (List.reverse (Text.toList suffix)),
          List.reverseReverse (Text.toList rest),
          Text.fromToList rest in
        rfl
  }

--| `stripPrefix` as a computation on the text: if the first `prefix.length`
--| characters are `prefix`, the rest follows; otherwise there is no result.
--| Use it when the other side of the proof is written with `take` and `drop`;
--| [`Text.stripPrefixSome`] is the form for reasoning about the equation.
theorem Text.stripPrefixTake ∀ (text prefix: Text):
    Text.stripPrefix text prefix
      = (if Text.take text (Text.length prefix) == prefix then Some (Text.drop text (Text.length prefix)) else None) :=
  match same: Text.take text (Text.length prefix) == prefix with
    | True =>
      (Text.stripPrefixSome text prefix (Text.drop text (Text.length prefix))).backward
        (Eq.trans
          (Eq.sym (Text.takeAppendDrop text (Text.length prefix)))
          (Eq.cong (front => Text.append front (Text.drop text (Text.length prefix))) same.read))
    | False =>
      match found: Text.stripPrefix text prefix with
        | None => rfl
        | Some rest =>
          Void.exfalso
            (same.read
              (Text.ext _ _
                (rewrite (Text.stripPrefixSome text prefix rest).forward found in
                  List.takeAppendLength (Text.toList prefix) (Text.toList rest) _ rfl)))

--| `stripSuffix` as a computation on the text: if the last `suffix.length`
--| characters are `suffix`, the characters before them are the result;
--| otherwise there is none. Use it when the other side of the proof is written
--| with `take` and `drop`; [`Text.stripSuffixSome`] is the form for reasoning
--| about the equation.
theorem Text.stripSuffixDrop ∀ (text suffix: Text):
    Text.stripSuffix text suffix
      = (if Text.drop text (Text.length text - Text.length suffix) == suffix then
           Some (Text.take text (Text.length text - Text.length suffix))
         else None) :=
  match same: Text.drop text (Text.length text - Text.length suffix) == suffix with
    | True =>
      (Text.stripSuffixSome text suffix (Text.take text (Text.length text - Text.length suffix))).backward
        (Eq.trans
          (Eq.sym (Text.takeAppendDrop text (Text.length text - Text.length suffix)))
          (Eq.cong (back => Text.append (Text.take text (Text.length text - Text.length suffix)) back) same.read))
    | False =>
      match found: Text.stripSuffix text suffix with
        | None => rfl
        | Some rest =>
          Void.exfalso
            (same.read
              (rewrite (Text.stripSuffixSome text suffix rest).forward found in
                Text.ext _ _
                  (List.dropAppendLength
                    (Text.toList rest)
                    (Text.toList suffix) _
                    (rewrite Text.lengthAppend rest suffix in omega))))

theorem Text.startsWithCharsAppend ∀ (t p: List Char): Text.startsWithChars p (List.append p t) = True := match p with
  | [] => rfl
  | [c, ..ps] =>
    Eq.trans
      (Eq.cong (b => if b then Text.startsWithChars ps (List.append ps t) else False) (Text.sameCharRefl c))
      (Text.startsWithCharsAppend t ps)

theorem Text.startsWithAppend ∀ (p t: Text): Text.startsWith (Text.append p t) p = True :=
  Text.startsWithCharsAppend (Text.toList t) (Text.toList p)

theorem Text.takeDropChars ∀ (n: Nat) (cs: List Char): List.append (List.take cs n) (List.drop cs n) = cs :=
  match n, cs with
    | Zero, cs => rfl
    | Succ n, [] => rfl
    | Succ n, [c, ..cs] => Eq.cong (Cons c) (Text.takeDropChars n cs)

theorem Text.takeAppendDrop ∀ (t: Text) (n: Nat): Text.append (Text.take t n) (Text.drop t n) = t :=
  Text.ext (Text.append (Text.take t n) (Text.drop t n)) t (Text.takeDropChars n (Text.toList t))

test "take and drop" := Text.take "héllo" 2 == "hé" ∧ Text.drop "héllo" 2 == "llo"
test "take and drop past the end" := Text.take "ab" 9 == "ab" ∧ Text.drop "ab" 9 == ""
test "stripPrefix" := Text.stripPrefix "L68" "L" == Some "68" ∧ Text.stripPrefix "R68" "L" == None
test "stripSuffix" := Text.stripSuffix "L68" "68" == Some "L" ∧ Text.stripSuffix "L68" "x" == None
test "startsWith and endsWith" :=
  Text.startsWith "abc" "ab" ∧ Text.endsWith "abc" "bc" ∧ ¬(Text.startsWith "abc" "abcd")
test "contains" := Text.contains "abcd" "bc" ∧ ¬(Text.contains "abcd" "ca") ∧ Text.contains "" ""
test "splitOn" := Text.splitOn "a, b" ", " == ["a", "b"] ∧ Text.splitOn "" "x" == [""]
test "splitOn empty separator" := Text.splitOn "abc" "" == ["abc"]
test "splitOn overlapping" := Text.splitOn "aaa" "aa" == ["", "a"]

--| The text `count` times over: `"ab".repeat 3` is `"ababab"`, and `text.repeat 0` is the empty text.
def Text.repeat (text: Text) (count: Nat): Text := List.replicate count text.toList |> .concat |> Text.fromList

--| The text cut into pieces of `size` characters, the last one shorter if need be:
--| `"abcde".chunksOf 2` is `["ab", "cd", "e"]`. As `List.chunksOf` does for
--| lists, `size = 0` gives the whole text as one chunk (none for an empty text).
def Text.chunksOf (text: Text) (size: Nat): List Text := text.toList.chunksOf size |> .map Text.fromList

test "Text.repeat" := Text.repeat "ab" 3 == "ababab" ∧ Text.repeat "ab" 0 == "" ∧ Text.repeat "" 4 == ""
test "Text.chunksOf" := Text.chunksOf "abcde" 2 == ["ab", "cd", "e"] ∧ Text.chunksOf "" 2 == []
test "Text.chunksOf zero" := Text.chunksOf "abc" 0 == ["abc"]
test "Text.words" :=
  "a  b\tc\n d ".words == ["a", "b", "c", "d"] ∧ "".words == [] ∧ "  ".words == [] ∧ "ab".words == ["ab"]
test "trim removes Unicode White_Space" := Text.trim "\u{A0}\u{3000}x y\u{85}\u{2028}\u{2003}" == "x y"
test "trim keeps the byte order mark" := Text.length (Text.trim "\u{FEFF}x\u{FEFF}") == 3
test "words splits on Unicode White_Space" := "a\u{A0}b\u{3000}c".words == ["a", "b", "c"]
test "isAsciiSpace is ASCII only" :=
  Char.isAsciiSpace ' ' ∧ ¬(Char.isAsciiSpace '\u{A0}') ∧ Char.isWhitespace '\u{A0}' ∧ ¬(Char.isWhitespace '\u{FEFF}')

--| Whether a character is an ASCII letter, `a` to `z` or `A` to `Z`.
def Char.isAsciiLetter (char: Char): Bool :=
  let code := char.toNat
  (97 <= code <= 122) || (65 <= code <= 90)

--| Whether a character is an ASCII letter or digit.
def Char.isAsciiAlphanumeric (char: Char): Bool := char.isAsciiLetter || char.isAsciiDigit

test "Char.isAsciiLetter" :=
  Char.isAsciiLetter 'a'
    ∧ Char.isAsciiLetter 'Z'
    ∧ ¬(Char.isAsciiLetter '0')
    ∧ ¬(Char.isAsciiLetter '.')
    ∧ ¬(Char.isAsciiLetter 'é')
test "Char.isAsciiDigit" :=
  Char.isAsciiDigit '0'
    ∧ Char.isAsciiDigit '7'
    ∧ Char.isAsciiDigit '9'
    ∧ ¬(Char.isAsciiDigit '/')
    ∧ ¬(Char.isAsciiDigit ':')
    ∧ ¬(Char.isAsciiDigit 'a')
    ∧ ¬(Char.isAsciiDigit '٣')
test "Char.isAsciiAlphanumeric" :=
  Char.isAsciiAlphanumeric 'q' ∧ Char.isAsciiAlphanumeric '7' ∧ ¬(Char.isAsciiAlphanumeric '#')

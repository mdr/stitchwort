import Parse.Problem (Expected, Literal, Message)
import Effect.AlwaysTreeOf (AlwaysCall)

-- `Parse.Reads` lemmas for the character pieces of Parse/Chars.sw and the
-- text runners; the generic ones are in Parse/Reads.sw.

theorem Parse.readsChar ∀ (expected: Char): Parse.Reads (() => Parse.char expected) (read u => read = [expected]) :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.satisfy "'${expected}'" (== expected)) (char => ()) _ (Parse.readsSatisfy))
    (read u h => match h with | Witness char (Both (Both one same) unit) => rewrite one, same.read in rfl)

theorem Parse.readsText ∀ (expected: Text):
    Parse.Reads (() => Parse.text expected) (read u => read = expected.toList) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.literal { items = expected.toList, same = Text.sameChar })
      (found =>
        if found then ()
        else
          Parse.note (Literal expected)
          Empty.absurd Parse.stop()) _
      (found read u => found = True ∧ read = [])
      (Parse.readsLiteral { items = expected.toList, same = Text.sameChar } Parse.sameCharExact)
      (found =>
        match found with
          | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Both rfl (And.left both))
          | False => state value after honest h => Void.exfalso (Result.errNotOk h)))
    (read u h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Both isTrue none))))) =>
          rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)

theorem Parse.readsTakeWhile ∀ (passes: Char → Bool):
    Parse.Reads (() => Parse.takeWhile passes) (read taken => taken = Text.fromList read ∧ read.all passes = True) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.span passes) Text.fromList _ (Parse.readsSpan passes)) (read taken h =>
    match h with | Witness chars (Both (Both same all) made) => rewrite made, <- same in Both rfl (rewrite same in all))

theorem Parse.readsTakeWhile1 [what: Text] [passes: Char → Bool]:
    Parse.Reads (() => Parse.takeWhile1 what passes) (read taken =>
      read ≠ [] ∧ read.all passes = True ∧ taken = Text.fromList read) :=
  Parse.readsSpanNonEmpty passes what Text.fromList

--| The value of decimal digits.
def Parse.digitsValue (digits: List Char): Nat := digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits

--| `nat` reads one or more digits, and gives their value.
theorem Parse.readsNat: Parse.Reads Parse.nat (read n =>
      read ≠ [] ∧ read.all Parse.isDigit = True ∧ n = Parse.digitsValue read) :=
  Parse.readsSpanNonEmpty Parse.isDigit "a number" Parse.digitsValue

--| What `Text.toNat` reads: a text of one or more ASCII digits is
--| `Some (Parse.digitsValue chars)`, and any other text is `None`. The
--| digits are those `Parse.nat` reads ([`Parse.readsNat`]).
--| For example `Text.toNat (Text.fromList chars)` is `Some` exactly when
--| `chars ≠ [] ∧ chars.all Parse.isDigit`.
theorem Text.toNatDigits ∀ (chars: List Char):
    Text.toNat (Text.fromList chars)
      = (if chars ≠ [] ∧ chars.all Parse.isDigit then Some (Parse.digitsValue chars) else None) :=
  match chars with
    | [] => rfl
    | [char, ..rest] =>
      rewrite List.allCong [char, ..rest] Parse.isDigit (char => char.digitValue.isSome) Char.isAsciiDigitDigitValue in
        Text.readDigitsValue 0 [char, ..rest]

--| `digit` reads one digit and gives its value.
theorem Parse.readsDigit: Parse.Reads Parse.digit (read d => ∃ (char: Char) => read = [char] ∧ char.toDigit = Some d) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.satisfy "a digit" Parse.isDigit)
      (char => Parse.need char.toDigit "expected a digit") _
      (char read d => read = [] ∧ char.toDigit = Some d)
      (Parse.readsSatisfy)
      (char => Parse.readsNeed char.toDigit _))
    (read d h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness char (Both split (Both (Both one digit) (Both none made))))) =>
          Witness char (Both (rewrite split, none, List.appendNil firstRead, one in rfl) made))

theorem Parse.readsSpaces: Parse.Reads Parse.spaces (read u => read.all Parse.isSpace = True) :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.span Parse.isSpace) (skipped => ()) _ (Parse.readsSpan Parse.isSpace))
    (read u h => match h with | Witness skipped (Both (Both same all) unit) => rewrite same in all)

theorem Parse.readsSpaces1: Parse.Reads Parse.spaces1 (read u => read ≠ [] ∧ read.all Parse.isSpace = True) :=
  Parse.readsWeaken
    (Parse.readsMap (() => Parse.takeWhile1 "a space" Parse.isSpace) (skipped => ()) _ (Parse.readsTakeWhile1))
    (read u h => match h with | Witness skipped (Both (Both some (Both all made)) unit) => Both some all)

--| What `token` reads: spaces, what `p` read, spaces.
def Parse.Padded (spec: List Char → a → Prop) (read: List Char) (value: a): Prop :=
  ∃ (before: List Char) => ∃ (middle: List Char) => ∃ (after: List Char) => read = before ++ (middle ++ after)
    ∧ before.all Parse.isSpace = True
    ∧ spec middle value
    ∧ after.all Parse.isSpace = True

theorem Parse.readsToken ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.token p) (Parse.Padded spec) :=
  Parse.readsWeaken
    (Parse.readsBind _ _ _
      (u => Parse.Then spec (v read w => read.all Parse.isSpace = True ∧ w = v))
      Parse.readsSpaces
      (u =>
        Parse.readsBind p
          (v =>
            Parse.spaces()
            v)
          spec
          (v read w => read.all Parse.isSpace = True ∧ w = v)
          reads
          (v =>
            Parse.readsWeaken (Parse.readsMap Parse.spaces (u => v) _ Parse.readsSpaces) (read w h =>
              match h with | Witness u (Both all same) => Both all same))))
    (read value h =>
      match h with
        | Witness before (Witness rest (Witness u (Both split (Both spaced inner)))) =>
          match inner with
            | Witness middle (Witness after (Witness v (Both split2 (Both holds (Both spacedAfter same))))) =>
              Witness before
                (Witness middle
                  (Witness after
                    (Both (rewrite split, split2 in rfl) (Both spaced (Both (rewrite same in holds) spacedAfter))))))

--| A line break: "\n" or "\r\n".
def Parse.LineBreak (read: List Char): Prop := read = ['\n'] ∨ read = ['\r', '\n']

--| "\n", else "\r\n", else fail: `newline`, and `lineEnd` away from the end.
theorem Parse.readsLineBreak ∀ (what: Text):
    Parse.Reads
      (() =>
        if Parse.literal { items = ['\n'], same = Text.sameChar } then ()
        else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
        else Parse.expected what)
      (read u => Parse.LineBreak read) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.literal { items = ['\n'], same = Text.sameChar })
      (found =>
        if found then ()
        else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
        else Parse.expected what) _
      (found read u => (found = True ∧ read = []) ∨ (found = False ∧ Parse.LineBreak read))
      (Parse.readsLiteral { items = ['\n'], same = Text.sameChar } Parse.sameCharExact)
      (found =>
        match found with
          | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Inl (Both rfl (And.left both)))
          | False =>
            Parse.readsWeaken
              (Parse.readsBind
                (() => Parse.literal { items = ['\r', '\n'], same = Text.sameChar })
                (found => if found then () else Parse.expected what) _
                (found read u => found = True ∧ read = [])
                (Parse.readsLiteral { items = ['\r', '\n'], same = Text.sameChar } Parse.sameCharExact)
                (found =>
                  match found with
                    | True => Parse.readsWeaken (Parse.readsPure ()) (read u both => Both rfl (And.left both))
                    | False => Parse.readsExpected what))
              (read u h =>
                match h with
                  | Witness firstRead
                      (Witness nextRead (Witness found (Both split (Both literal (Both isTrue none))))) =>
                    Inr (Both rfl (Inr (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl))))))
    (read u h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness found (Both split (Both literal (Inl (Both isTrue none)))))) =>
          Inl (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)
        | Witness firstRead
            (Witness nextRead (Witness found (Both split (Both literal (Inr (Both isFalse breaks)))))) =>
          rewrite split, literal, isFalse in breaks)

theorem Parse.readsNewline: Parse.Reads Parse.newline (read u => Parse.LineBreak read) :=
  Parse.readsLineBreak "a line break"

--| `lineEnd` reads a line break, or nothing (at the end).
theorem Parse.readsLineEnd: Parse.Reads Parse.lineEnd (read u => read = [] ∨ Parse.LineBreak read) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at =>
        if at.left == 0 then ()
        else if Parse.literal { items = ['\n'], same = Text.sameChar } then ()
        else if Parse.literal { items = ['\r', '\n'], same = Text.sameChar } then ()
        else Parse.expected "the end of the line") _
      (at read u => read = [] ∨ Parse.LineBreak read)
      Parse.readsMark
      (at =>
        Parse.readsIf _
          (() => ()) _ _
          (Parse.readsWeaken (Parse.readsPure ()) (read u both => Inl (And.left both)))
          (Parse.readsWeaken (Parse.readsLineBreak "the end of the line") (read u breaks => Inr breaks))))
    (read u h => match Parse.thenNothing _ read u h with | Witness at holds => holds)

theorem Parse.readsBefore ∀ (value: a) (suffix: Text):
    Parse.Reads (() => Parse.before value suffix) (read v => read = suffix.toList ∧ v = value) :=
  Parse.readsWeaken (Parse.readsMap (() => Parse.text suffix) (u => value) _ (Parse.readsText suffix)) (read v h =>
    match h with | Witness u (Both same made) => Both same made)

--| What `pick` tries: the first choice whose word comes next.
def Parse.Picked (choices: List (Text, a)) (read: List Char) (choice: (Text, a)): Prop :=
  choice ∈ choices ∧ read = choice.fst.toList

theorem Parse.readsFindWord ∀ (choices: List (Text, a)):
    Parse.Reads
      (() => choices.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
      (Parse.Maybe (Parse.Picked choices)) :=
  match choices with
    | [] => Parse.readsWeaken (Parse.readsPure None) (read found both => rewrite And.right both in And.left both)
    | [choice, ..rest] =>
      Parse.readsWeaken
        (Parse.readsBind
          (() => Parse.literal { items = choice.fst.toList, same = Text.sameChar })
          (found =>
            if found then Some choice
            else rest.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar })) _
          (found read result =>
            (found = True ∧ read = [] ∧ result = Some choice)
              ∨ (found = False ∧ Parse.Maybe (Parse.Picked rest) read result))
          (Parse.readsLiteral { items = choice.fst.toList, same = Text.sameChar } Parse.sameCharExact)
          (found =>
            match found with
              | True => Parse.readsWeaken (Parse.readsPure (Some choice)) (read result both => Inl (Both rfl both))
              | False => Parse.readsWeaken (Parse.readsFindWord rest) (read result holds => Inr (Both rfl holds))))
        (read result h =>
          match h with
            | Witness firstRead
                (Witness nextRead (Witness found (Both split (Both literal (Inl (Both isTrue (Both none same))))))) =>
              rewrite same in Both (Inl rfl) (rewrite split, none, List.appendNil firstRead, literal, isTrue in rfl)
            | Witness firstRead
                (Witness nextRead (Witness found (Both split (Both literal (Inr (Both isFalse later)))))) =>
              Parse.findLater choice rest read result firstRead nextRead (rewrite literal, isFalse in rfl) split later)

theorem Parse.findLater ∀ (first: (Text, a)) (rest: List (Text, a)) (read: List Char)
    (result: Option (Text, a)) (firstRead nextRead: List Char)
    (none: firstRead = [])
    (split: read = firstRead ++ nextRead)
    (later: Parse.Maybe (Parse.Picked rest) nextRead result):
    Parse.Maybe (Parse.Picked [first, ..rest]) read result :=
  match result with
    | None => rewrite split, none in later
    | Some choice =>
      match later with
        | Both member same => Both (Inr member) (rewrite split, none in same)

--| `pick` reads one of its words, and gives that word's value.
theorem Parse.readsPick ∀ (choices: List (Text, a)):
    Parse.Reads (() => Parse.pick choices) (read value =>
      ∃ (word: Text) => (word, value) ∈ choices ∧ read = word.toList) :=
  Parse.readsWeaken
    [weaker := (read value => ∃ (word: Text) => (word, value) ∈ choices ∧ read = word.toList)]
    (Parse.readsBind
      (() => choices.find (choice => Parse.literal { items = choice.fst.toList, same = Text.sameChar }))
      (found =>
        match found with
          | Some (word, value) => value
          | None =>
            Parse.noteWords choices
            Empty.absurd Parse.stop()) _
      (found read value => read = [] ∧ ∃ (word: Text) => found = Some (word, value))
      (Parse.readsFindWord choices)
      (found =>
        match found with
          | Some (word, value) => Parse.readsWeaken (Parse.readsPure value) (read v both =>
            Both (And.left both) (Witness word (rewrite And.right both in rfl)))
          | None => Parse.readsThenStop (() => Parse.noteWords choices) _))
    (read value h =>
      match h with
        | Witness firstRead
            (Witness nextRead (Witness found (Both split (Both picked (Both none (Witness word same)))))) =>
          match (rewrite same at picked in picked: Parse.Picked choices firstRead (word, value)) with
            | Both member read =>
              Witness word (Both member (rewrite split, none, List.appendNil firstRead, read in rfl)))

--| `lines p`: one value per line, line breaks between.
theorem Parse.readsLines ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.lines p) (Parse.SepBy spec (read u => Parse.LineBreak read)) :=
  Parse.readsSepBy1 p Parse.newline spec _ reads Parse.readsNewline

--| `grid cell`: rows of one or more cells, line breaks between.
theorem Parse.readsGrid ∀ (cell: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads cell spec):
    Parse.Reads
      (() => Parse.grid cell)
      (Parse.SepBy (read row => Parse.Each spec read row.toList) (read u => Parse.LineBreak read)) :=
  Parse.readsLines _ _ (Parse.readsMany1 cell spec reads)

--| What `looseRow cell` reads: its cells, then a line break or nothing.
def Parse.LooseRow (spec: List Char → a → Prop) (read: List Char) (cells: List a): Prop :=
  ∃ (cellsRead: List Char) => ∃ (endRead: List Char) => read = cellsRead ++ endRead
    ∧ Parse.Each spec cellsRead cells
    ∧ (endRead = [] ∨ Parse.LineBreak endRead)

theorem Parse.readsLooseRow ∀ (cell: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads cell spec):
    Parse.Reads (() => Parse.looseRow cell) (Parse.LooseRow spec) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (at =>
        if at.left == 0 then Empty.absurd Parse.stop()
        else
          let cells := Parse.many cell
          Parse.lineEnd()
          cells) _
      (at => Parse.LooseRow spec)
      Parse.readsMark
      (at =>
        Parse.readsIf _
          (() => Empty.absurd Parse.stop())
          (() =>
            let cells := Parse.many cell
            Parse.lineEnd()
            cells) _
          (Parse.readsStop _)
          (Parse.readsWeaken
            (Parse.readsBind
              (() => Parse.many cell)
              (cells =>
                Parse.lineEnd()
                cells) _
              (cells read row => (read = [] ∨ Parse.LineBreak read) ∧ row = cells)
              (Parse.readsMany cell spec reads)
              (cells =>
                Parse.readsWeaken (Parse.readsMap Parse.lineEnd (u => cells) _ Parse.readsLineEnd) (read row h =>
                  match h with | Witness u (Both ends same) => Both ends same)))
            (read row h =>
              match h with
                | Witness cellsRead (Witness endRead (Witness cells (Both split (Both each (Both ends same))))) =>
                  Witness cellsRead (Witness endRead (Both split (Both (rewrite same in each) ends)))))))
    (read row h => match Parse.thenNothing (at => Parse.LooseRow spec) read row h with | Witness at holds => holds)

--| `looseGrid cell`: one row per line, each its cells and its line break.
theorem Parse.readsLooseGrid ∀ (cell: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads cell spec):
    Parse.Reads (() => Parse.looseGrid cell) (Parse.Each (Parse.LooseRow spec)) :=
  Parse.readsMany _ _ (Parse.readsLooseRow cell spec reads)

--| One line of `eachLine`, read.
theorem Parse.eachLineOne ∀ (index: Nat) (line: Text) (parser: () → {Parse Char} a) (value: a)
    (h: Fail.toResult (() =>
      let chars := line.toList
      match Parse.whole chars parser with
        | Ok value => value
        | Err failure =>
          Fail.fail
            "line ${index + 1}, column ${failure.offset + 1}: ${failure.describe chars "the end of the line" "a line break"}")
      = Ok value):
    Parse.whole line.toList parser = Ok value :=
  match e: Parse.whole line.toList parser with | Ok v => rewrite Result.okInjective h in rfl

--| `eachLine input p` succeeded: one value per line, each `spec` of all of
--| its line.
theorem Parse.eachLineReads ∀ (input: Text) (p: () → {Parse Char} a) (spec: List Char → a → Prop) (values: List a)
    (h: Fail.toResult (() => Parse.eachLine input p) = Ok values)
    (reads: Parse.Reads p spec):
    List.All2 spec (input.lines.map Text.toList) values :=
  let traversed := rewrite Fail.toResultMap _ input.lines.withIndex at h in h
  List.all2MapLeft Text.toList spec input.lines values
    (List.all2WithIndex
      (line v => spec line.toList v)
      0
      input.lines
      values
      (Result.traverseAll2 _
        (entry v => spec entry.snd.toList v)
        (entry v read =>
          match entry with
            | (index, line) => Parse.wholeReads line.toList p spec v reads (Parse.eachLineOne index line p v read))
        input.lines.withIndex
        values
        traversed))

--| `pick` over values each with its own word, `word x` for `x`: it reads one
--| of the values' words and gives that value. A table made from a printer
--| this way makes the parser's guarantee a fact about the printer.
theorem Parse.readsPickBy ∀ (values: List a) (word: a → Text):
    Parse.Reads (() => Parse.pick (values.map (value => (word value, value)))) (read value =>
      value ∈ values ∧ read = (word value).toList) :=
  Parse.readsWeaken (Parse.readsPick (values.map (value => (word value, value)))) (read value h =>
    match h with
      | Witness found (Both member same) =>
        match List.memMapElim (value => (word value, value)) (found, value) values member with
          | Witness original (Both isIn made) =>
            let valueSame: original = value := Pair.mkInjectiveSnd made
            let wordSame: word original = found := Pair.mkInjectiveFst made
            rewrite <- valueSame in Both isIn (rewrite same, <- wordSame in rfl))

--| A repetition each of whose parts is one character, `f` of its value,
--| read the values' characters.
theorem Parse.eachChars ∀ (f: a → Char) (read: List Char) (values: List a)
    (each: Parse.Each (read value => read = [f value]) read values):
    read = values.map f :=
  match values with
    | [] => each
    | [value, ..values] =>
      match each with
        | Witness first (Witness rest (Both split (Both one others))) =>
          rewrite split, one, Parse.eachChars f rest values others in rfl

--| `line text p` succeeded: `p` read all of `text` but a final line break.
theorem Parse.lineReads ∀ (text: Text) (p: () → {Parse Char} a) (spec: List Char → a → Prop) (value: a)
    (h: Fail.toResult (() => Parse.line text p) = Ok value)
    (reads: Parse.Reads p spec):
    ∃ (read: List Char) => ∃ (ending: List Char) => text.toList = read ++ ending
      ∧ spec read value
      ∧ (ending = [] ∨ Parse.LineBreak ending) :=
  let readsAll :=
    Parse.readsBind p
      (value =>
        let finalLineBreak := Parse.optional Parse.newline
        value)
      spec _
      reads
      (v => Parse.readsMap (() => Parse.optional Parse.newline) (found => v) _ (Parse.readsOptional Parse.readsNewline))
  match Parse.wholeReads text.toList
    (() => Parse.withFinalLineBreak p) _
    value
    readsAll
    (Parse.runnerOk text.toList (() => Parse.withFinalLineBreak p) (Parse.lineMessage text.toList) value h) with
    | Witness read (Witness ending (Witness v (Both split (Both holds (Witness found (Both ends same)))))) =>
      Witness read (Witness ending (Both split (Both (rewrite same in holds) (Parse.lineEnding ending found ends))))

theorem Parse.lineEnding ∀ (ending: List Char) (found: Option ())
    (none: Parse.Maybe (read u => Parse.LineBreak read) ending found):
    ending = [] ∨ Parse.LineBreak ending :=
  match found, none with
    | None, none => Inl none
    | Some u, breaks => Inr breaks

theorem Parse.readsExtraBlankLine ∀ (start: Parse.Mark Char) (spec: List Char → () → Prop):
    Parse.Reads (() => Parse.extraBlankLine start) spec :=
  Parse.readsThenStop
    (() => (Parse.reset start; Parse.newline(); Parse.note (Message "expected the end of the input, got a blank line")))
    spec

--| `withFinalLineBreaks (() => v)` reads final line breaks, and gives `v`.
theorem Parse.readsFinalLineBreaks ∀ (v: a):
    Parse.Reads (() => Parse.withFinalLineBreaks (() => v)) (read w =>
      read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v) :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.mark())
      (start =>
        let finalLineBreaks := Parse.span (char => char == '\n' ∨ char == '\r')
        if finalLineBreaks == [] then Parse.note (Expected "a line break")
        else if finalLineBreaks == ['\n'] then ()
        else if finalLineBreaks == ['\r', '\n'] then ()
        else if start.left == finalLineBreaks.length then ()
        else Parse.extraBlankLine start
        v)
      (read m => read = [])
      (start read w => read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v)
      Parse.readsMark
      (start =>
        Parse.readsWeaken
          (Parse.readsBind _ _ _ (breaks read w => read = [] ∧ w = v) (Parse.readsSpan _) (breaks =>
            Parse.readsWeaken
              (Parse.readsBind _ _
                (read u => read = [])
                (u read w => read = [] ∧ w = v)
                (Parse.readsIf
                  (breaks == [])
                  (() => Parse.note (Expected "a line break"))
                  (() =>
                    if breaks == ['\n'] then ()
                    else if breaks == ['\r', '\n'] then ()
                    else if start.left == breaks.length then ()
                    else Parse.extraBlankLine start)
                  (read u => read = [])
                  (Parse.readsNote (Expected "a line break"))
                  (Parse.readsIf
                    (breaks == ['\n'])
                    (() => ())
                    (() =>
                      if breaks == ['\r', '\n'] then ()
                      else if start.left == breaks.length then ()
                      else Parse.extraBlankLine start)
                    (read u => read = [])
                    (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                    (Parse.readsIf
                      (breaks == ['\r', '\n'])
                      (() => ())
                      (() => if start.left == breaks.length then () else Parse.extraBlankLine start)
                      (read u => read = [])
                      (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                      (Parse.readsIf
                        (start.left == breaks.length)
                        (() => ())
                        (() => Parse.extraBlankLine start)
                        (read u => read = [])
                        (Parse.readsWeaken (Parse.readsPure ()) (read u h => And.left h))
                        (Parse.readsExtraBlankLine start _)))))
                (u => Parse.readsPure v))
              (read w h =>
                match h with
                  | Witness firstRead (Witness nextRead (Witness u (Both split (Both none (Both none2 same))))) =>
                    Both (rewrite split, none, none2 in rfl) same)))
          (read w h =>
            match h with
              | Witness firstRead
                  (Witness nextRead (Witness breaks (Both split (Both (Both taken all) (Both none same))))) =>
                Both (rewrite split, none, List.appendNil firstRead, taken in all) same)))
    (read w h =>
      match h with
        | Witness firstRead (Witness nextRead (Witness m (Both split (Both none holds)))) =>
          rewrite split, none in holds)

--| `all input p` succeeded: `p` read all of `input` but final line breaks.
theorem Parse.allReads ∀ (input: Text) (p: () → {Parse Char} a) (spec: List Char → a → Prop) (value: a)
    (h: Fail.toResult (() => Parse.all input p) = Ok value)
    (reads: Parse.Reads p spec):
    ∃ (read: List Char) => ∃ (ending: List Char) => input.toList = read ++ ending
      ∧ spec read value
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True :=
  let readsAll :=
    Parse.readsBind p
      (value => Parse.withFinalLineBreaks (() => value))
      spec
      (v read w => read.all (char => char == '\n' ∨ char == '\r') = True ∧ w = v)
      reads
      Parse.readsFinalLineBreaks
  match Parse.wholeReads input.toList
    (() => Parse.withFinalLineBreaks p) _
    value
    readsAll
    (Parse.runnerOk input.toList (() => Parse.withFinalLineBreaks p) (Parse.allMessage input.toList) value h) with
    | Witness read (Witness ending (Witness v (Both split (Both holds (Both all same))))) =>
      Witness read (Witness ending (Both split (Both (rewrite same in holds) all)))

--| What `int` reads: digits, with an optional '+' or '-' in front.
def Parse.IntRead (read: List Char) (n: Int): Prop :=
  ∃ (digits: List Char) => digits ≠ []
    ∧ digits.all Parse.isDigit = True
    ∧ ((read = ['-', ..digits] ∧ n = -(Parse.digitsValue digits).toInt)
      ∨ (read = ['+', ..digits] ∧ n = (Parse.digitsValue digits).toInt)
      ∨ (read = digits ∧ n = (Parse.digitsValue digits).toInt))

theorem Parse.readsInt: Parse.Reads Parse.int Parse.IntRead :=
  Parse.readsWeaken
    (Parse.readsBind
      (() => Parse.literal { items = ['-'], same = Text.sameChar })
      (negative =>
        if negative then -(Parse.nat().toInt)
        else if Parse.literal { items = ['+'], same = Text.sameChar } then Parse.nat().toInt
        else Parse.nat().toInt) _
      (negative read n =>
        ∃ (digits: List Char) => digits ≠ []
          ∧ digits.all Parse.isDigit = True
          ∧ ((negative = True ∧ read = digits ∧ n = -(Parse.digitsValue digits).toInt)
            ∨ (negative = False
              ∧ ((read = ['+', ..digits] ∧ n = (Parse.digitsValue digits).toInt)
                ∨ (read = digits ∧ n = (Parse.digitsValue digits).toInt)))))
      (Parse.readsLiteral { items = ['-'], same = Text.sameChar } Parse.sameCharExact)
      (negative =>
        match negative with
          | True =>
            Parse.readsWeaken
              (Parse.readsMap
                (() => Parse.nat().toInt)
                (i => -i) _
                (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat))
              (read n h =>
                match h with
                  | Witness i (Both (Witness m (Both (Both some (Both all value)) made)) negated) =>
                    Witness read
                      (Both some (Both all (Inl (Both rfl (Both rfl (rewrite negated, made, value in rfl)))))))
          | False =>
            Parse.readsWeaken
              (Parse.readsBind
                (() => Parse.literal { items = ['+'], same = Text.sameChar })
                (plus => if plus then Parse.nat().toInt else Parse.nat().toInt) _
                (plus read n =>
                  ∃ (digits: List Char) => digits ≠ []
                    ∧ digits.all Parse.isDigit = True
                    ∧ read = digits
                    ∧ n = (Parse.digitsValue digits).toInt)
                (Parse.readsLiteral { items = ['+'], same = Text.sameChar } Parse.sameCharExact)
                (plus =>
                  match plus with
                    | True => Parse.readsWeaken (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat) (read n h =>
                      match h with
                        | Witness m (Both (Both some (Both all value)) made) =>
                          Witness read (Both some (Both all (Both rfl (rewrite made, value in rfl)))))
                    | False => Parse.readsWeaken (Parse.readsMap Parse.nat (m => m.toInt) _ Parse.readsNat) (read n h =>
                      match h with
                        | Witness m (Both (Both some (Both all value)) made) =>
                          Witness read (Both some (Both all (Both rfl (rewrite made, value in rfl)))))))
              (read n h =>
                match h with
                  | Witness plusRead
                      (Witness digitsRead
                        (Witness plus
                          (Both split (Both literal (Witness digits (Both some (Both all (Both same value)))))))) =>
                    match plus with
                      | True =>
                        Witness digits
                          (Both some
                            (Both all (Inr (Both rfl (Inl (Both (rewrite split, literal, same in rfl) value))))))
                      | False =>
                        Witness digits
                          (Both some
                            (Both all (Inr (Both rfl (Inr (Both (rewrite split, literal, same in rfl) value)))))))))
    (read n h =>
      match h with
        | Witness firstRead
            (Witness nextRead
              (Witness negative (Both split (Both literal (Witness digits (Both nonEmpty (Both all choice))))))) =>
          match choice with
            | Inl (Both isTrue (Both sameRead value)) =>
              Witness digits
                (Both nonEmpty (Both all (Inl (Both (rewrite split, literal, isTrue, sameRead in rfl) value))))
            | Inr (Both isFalse inner) =>
              match inner with
                | Inl (Both plus value) =>
                  Witness digits
                    (Both nonEmpty (Both all (Inr (Inl (Both (rewrite split, literal, isFalse, plus in rfl) value)))))
                | Inr (Both noSign value) =>
                  Witness digits
                    (Both nonEmpty
                      (Both all (Inr (Inr (Both (rewrite split, literal, isFalse, noSign in rfl) value))))))

--| `sectionLineFrom start q` that let the rest succeed: `q` succeeded on
--| its own. It passes each of `q`'s operations on, and adds a note only
--| when `q` stops.
theorem Parse.runFromSectionLineFromOkTree ∀ (q: () → {Parse Char} a)
    (tree: Effect.AlwaysTree (x => Unit) (q ()))
    (start: Parse.Mark Char) (s: Parse.State Char) (k: a → {Parse Char} b) (w: b)
    (h: Parse.runFrom s (() => k (Parse.sectionLineFrom start q)) = Ok w):
    ∃ (v: a) => ∃ (after: Parse.State Char) => Parse.runFrom s (() => (q(), Parse.mark())) = Ok (v, after.at)
      ∧ Parse.runFrom after (() => k v) = Ok w :=
  match reify q with
    | return x => Witness x (Witness s (Both rfl h))
    | Parse.span passes, r =>
      match tree with
        | AlwaysCall later =>
          Parse.runFromSectionLineFromOkTree
            (() => r (s.span passes).fst)
            (later (s.span passes).fst)
            start
            (s.span passes).snd
            k
            w
            h
    | Parse.next passes, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromNext s passes (y => (r y, Parse.mark())) in
            Parse.runFromSectionLineFromOkTree
              (() => r (s.next passes).fst)
              (later (s.next passes).fst)
              start
              (s.next passes).snd
              k
              w
              (Eq.trans (Eq.sym (Parse.runFromNext s passes _)) h)
    | Parse.literal literal, r =>
      match tree with
        | AlwaysCall later =>
          rewrite Parse.runFromLiteral s literal (y => (r y, Parse.mark())) in
            Parse.runFromSectionLineFromOkTree
              (() => r (s.literal literal).fst)
              (later (s.literal literal).fst)
              start
              (s.literal literal).snd
              k
              w
              (Eq.trans (Eq.sym (Parse.runFromLiteral s literal _)) h)
    | Parse.mark u, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r s.at) (later s.at) start s k w h
    | Parse.reset at, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r ()) (later ()) start { s | at } k w h
    | Parse.note problem, r =>
      match tree with
        | AlwaysCall later => Parse.runFromSectionLineFromOkTree (() => r ()) (later ()) start (s.note problem) k w h
    | Parse.stop u, r => Void.exfalso (Result.errNotOk h)
    | Parse.fatal message, r => Void.exfalso (Result.errNotOk h)

--| `sectionLine p` reads what `p` read.
theorem Parse.readsSectionLine ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.sectionLine p) spec :=
  state value after honest h =>
    match Parse.runFromSectionLineFromOkTree p
      (Effect.Always.tree (x => Unit) (p ()) (Effect.alwaysUnit (p ())))
      state.at
      state
      (x => (x, Parse.mark()))
      (value, after)
      h with
      | Witness v (Witness middle (Both ran rest)) =>
        Parse.readsFromRun p spec reads state value after honest v middle ran rest

--| What `blankLine` reads: a line break, spaces and tabs, a line break.
def Parse.BlankLine (read: List Char): Prop :=
  ∃ (first: List Char) => ∃ (middle: List Char) => ∃ (last: List Char) => read = first ++ (middle ++ last)
    ∧ Parse.LineBreak first
    ∧ middle.all Parse.isSpace = True
    ∧ Parse.LineBreak last

theorem Parse.readsBlankLine: Parse.Reads Parse.blankLine (read u => Parse.BlankLine read) :=
  Parse.readsLabelWhole "a blank line"
    (() =>
      Parse.newline()
      Parse.spaces()
      Parse.newline()) _
    (Parse.readsWeaken
      (Parse.readsBind Parse.newline
        (u =>
          Parse.spaces()
          Parse.newline()) _
        (u => Parse.Then (read u => read.all Parse.isSpace = True) (u read v => Parse.LineBreak read))
        Parse.readsNewline
        (u =>
          Parse.readsBind Parse.spaces
            (u => Parse.newline()) _
            (u read v => Parse.LineBreak read)
            Parse.readsSpaces
            (u => Parse.readsNewline)))
      (read u h =>
        match h with
          | Witness first (Witness rest (Witness u1 (Both split (Both breaks inner)))) =>
            match inner with
              | Witness middle (Witness last (Witness u2 (Both split2 (Both spaced breaks2)))) =>
                Witness first
                  (Witness middle
                    (Witness last (Both (rewrite split, split2 in rfl) (Both breaks (Both spaced breaks2)))))))

--| `sections p`: `p`'s blocks, a blank line between each two.
theorem Parse.readsSections ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.sections p) (Parse.SepBy spec (read u => Parse.BlankLine read)) :=
  Parse.readsSepBy1 p Parse.blankLine spec _ reads Parse.readsBlankLine

--| What `section p` reads: one value per line, line breaks between, then a
--| blank line.
def Parse.Section (spec: List Char → a → Prop) (read: List Char) (values: NonEmptyList a): Prop :=
  ∃ (linesRead: List Char) => ∃ (blankRead: List Char) => read = linesRead ++ blankRead
    ∧ Parse.SepBy spec (read u => Parse.LineBreak read) linesRead values
    ∧ Parse.BlankLine blankRead

theorem Parse.readsSection ∀ (p: () → {Parse Char} a) (spec: List Char → a → Prop)
    (reads: Parse.Reads p spec):
    Parse.Reads (() => Parse.section p) (Parse.Section spec) :=
  Parse.readsWeaken
    (Parse.readsBind p
      (first =>
        let rest := Parse.many (() =>
          Parse.newline()
          Parse.sectionLine p)
        Parse.blankLine()
        NonEmptyList.cons first rest)
      spec
      (first =>
        Parse.Then (Parse.Each (Parse.Then (read u => Parse.LineBreak read) (u => spec))) (rest read values =>
          Parse.BlankLine read ∧ values = NonEmptyList.cons first rest))
      reads
      (first =>
        Parse.readsBind
          (() =>
            Parse.many (() =>
              Parse.newline()
              Parse.sectionLine p))
          (rest =>
            Parse.blankLine()
            NonEmptyList.cons first rest) _
          (rest read values => Parse.BlankLine read ∧ values = NonEmptyList.cons first rest)
          (Parse.readsMany _ _
            (Parse.readsBind Parse.newline (u => Parse.sectionLine p) _ (u => spec) Parse.readsNewline (u =>
              Parse.readsSectionLine p spec reads)))
          (rest =>
            Parse.readsWeaken
              (Parse.readsMap Parse.blankLine (u => NonEmptyList.cons first rest) _ Parse.readsBlankLine)
              (read values h => match h with | Witness u (Both blank same) => Both blank same))))
    (read values h =>
      match h with
        | Witness firstRead (Witness restRead (Witness first (Both split (Both holds inner)))) =>
          match inner with
            | Witness eachRead (Witness blankRead (Witness rest (Both split2 (Both each (Both blank same))))) =>
              Witness
                (firstRead ++ eachRead)
                (Witness blankRead
                  (Both
                    (rewrite split, split2, List.appendAssoc firstRead eachRead blankRead in rfl)
                    (Both
                      (rewrite same in
                        Witness firstRead (Witness eachRead (Witness first (Both rfl (Both holds (Both rfl each))))))
                      blank))))

-- `sections` over the lines of the input (SW-1401).

--| A line break between `read` and what follows it ends a line there,
--| whichever of "\n" and "\r\n" it is: the lines are those of `read` with
--| its break, then those of the rest.
theorem Parse.linesBreak ∀ (read first rest: List Char)
    (breaks: Parse.LineBreak first):
    Text.lines (MkText (read ++ (first ++ rest))) = Text.lines (MkText (read ++ first)) ++ Text.lines (MkText rest) :=
  match breaks with
    | Inl feed => rewrite feed in Text.linesAppend read rest
    | Inr both =>
      rewrite both in
        Eq.trans
          (Eq.cong (l => Text.lines (MkText l)) (Eq.sym (List.appendAssoc read ['\r'] ['\n', ..rest])))
          (Eq.trans
            (Text.linesAppend (read ++ ['\r']) rest)
            (Eq.cong (l => Text.lines (MkText l) ++ Text.lines (MkText rest)) (List.appendAssoc read ['\r'] ['\n'])))

--| `read`, a blank line, and `rest`: the lines of `read` with its line
--| break, a line of the blank line's spaces and tabs, and the lines of the
--| rest. The blank line's own breaks are `first` and `last`.
theorem Parse.linesBlank ∀ (read first middle last rest: List Char)
    (firstBreak: Parse.LineBreak first)
    (spaced: middle.all Parse.isSpace = True)
    (lastBreak: Parse.LineBreak last):
    Text.lines (MkText (read ++ (first ++ (middle ++ (last ++ rest)))))
      = Text.lines (MkText (read ++ first)) ++ [MkText middle, ..Text.lines (MkText rest)] :=
  let plain: List.All
    (c => Char.isLineFeedCode (Char.toNat c) = False ∧ Char.isCarriageReturnCode (Char.toNat c) = False)
    middle :=
    List.allImplies _ _ (c isSpace => Text.spaceTabPlain c isSpace) middle (List.allToAll Parse.isSpace middle spaced)
  let onlyLine: Text.lines (MkText (middle ++ (last ++ rest))) = [MkText middle, ..Text.lines (MkText rest)] :=
    match lastBreak with
      | Inl feed => rewrite feed in Text.linesPlainLine middle rest plain
      | Inr both => rewrite both in Text.linesPlainLineReturn middle rest plain
  Eq.trans
    (Parse.linesBreak read first (middle ++ (last ++ rest)) firstBreak)
    (Eq.cong (l => Text.lines (MkText (read ++ first)) ++ l) onlyLine)

--| What `sections` read, as `lines`: the first value's section, a line
--| break, a blank line, then the next section, and so on, the last
--| section's characters followed by `ending`. Each section's `read` is
--| `spec` of its value, and the lines are those of the section with the line
--| break after it, the blank line's spaces and tabs as a line, and the lines
--| of what follows. What the section's lines look like in terms of `read`
--| is [`Text.unlinesLines`] when it has no carriage return.
def Parse.SectionsLines (spec: List Char → a → Prop) (value: a): (values: List a) → (lines: List Text) → Prop
  | [], lines =>
    ∃ (read: List Char) => ∃ (ending: List Char) => spec read value
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True
      ∧ lines = Text.lines (MkText (read ++ ending))
  | [next, ..more], lines =>
    ∃ (read: List Char) => ∃ (first: List Char) => ∃ (middle: List Char) => ∃ (last: List Char) =>
      ∃ (rest: List Text) => spec read value
        ∧ Parse.LineBreak first
        ∧ middle.all Parse.isSpace = True
        ∧ Parse.LineBreak last
        ∧ lines = Text.lines (MkText (read ++ first)) ++ [MkText middle, ..rest]
        ∧ Parse.SectionsLines spec next more rest

theorem Parse.appendBlank ∀ (first middle last nextRead afterChunk ending: List Char):
    ((((first ++ (middle ++ last)) ++ nextRead) ++ afterChunk) ++ ending)
      = first ++ (middle ++ (last ++ (nextRead ++ (afterChunk ++ ending)))) :=
  rewrite List.appendAssoc ((first ++ (middle ++ last)) ++ nextRead) afterChunk ending,
      List.appendAssoc (first ++ (middle ++ last)) nextRead (afterChunk ++ ending),
      List.appendAssoc first (middle ++ last) (nextRead ++ (afterChunk ++ ending)),
      List.appendAssoc middle last (nextRead ++ (afterChunk ++ ending)) in
    rfl

theorem Parse.sectionsLinesEach ∀ (spec: List Char → a → Prop) (ending: List Char)
    (ended: ending.all (char => char == '\n' ∨ char == '\r') = True)
    (rests: List a) (value: a) (read afterFirst: List Char) (holds: spec read value)
    (each: Parse.Each (Parse.Then (read (u: ()) => Parse.BlankLine read) (u => spec)) afterFirst rests):
    Parse.SectionsLines spec value rests (Text.lines (MkText (read ++ (afterFirst ++ ending)))) :=
  match rests with
    | [] => rewrite each in Witness read (Witness ending (Both holds (Both ended rfl)))
    | [next, ..more] =>
      match each with
        | Witness chunk
            (Witness afterChunk
              (Both split
                (Both
                  (Witness blankRead (Witness nextRead (Witness u (Both split2 (Both blank nextHolds)))))
                  others))) =>
          match blank with
            | Witness first
                (Witness middle (Witness last (Both blankSplit (Both firstBreak (Both spaced lastBreak))))) =>
              let lined: Text.lines (MkText (read ++ (afterFirst ++ ending)))
                = Text.lines (MkText (read ++ first))
                  ++ [MkText middle, ..Text.lines (MkText (nextRead ++ (afterChunk ++ ending)))] :=
                rewrite split, split2, blankSplit, Parse.appendBlank first middle last nextRead afterChunk ending in
                  Parse.linesBlank read first middle last
                    (nextRead ++ (afterChunk ++ ending))
                    firstBreak
                    spaced
                    lastBreak
              rewrite lined in
                Witness read
                  (Witness first
                    (Witness middle
                      (Witness last
                        (Witness
                          (Text.lines (MkText (nextRead ++ (afterChunk ++ ending))))
                          (Both holds
                            (Both firstBreak
                              (Both spaced
                                (Both lastBreak
                                  (Both rfl
                                    (Parse.sectionsLinesEach spec ending ended more next nextRead afterChunk nextHolds
                                        others))))))))))

--| What `sections` read, followed by `ending`, as lines: the lines of the
--| whole are `SectionsLines`. For a parser that maps `sections p`, such as
--| `Parse.sections p |> .toList`, after [`Parse.allReads`].
theorem Parse.sectionsLinesRead ∀ (spec: List Char → a → Prop) (values: NonEmptyList a) (read ending: List Char)
    (written: Parse.SepBy spec (read u => Parse.BlankLine read) read values)
    (ended: ending.all (char => char == '\n' ∨ char == '\r') = True):
    Parse.SectionsLines spec values.head values.tail (Text.lines (MkText (read ++ ending))) :=
  match written with
    | Witness firstRead (Witness afterFirst (Witness v (Both split (Both holds (Both isHead each))))) =>
      rewrite split, <- isHead, List.appendAssoc firstRead afterFirst ending in
        Parse.sectionsLinesEach spec ending ended values.tail v firstRead afterFirst holds each

--| `Parse.all input (() => Parse.sections p)` succeeded: the input's lines
--| are the sections' lines with a line of spaces and tabs between each two,
--| each section read by `spec` ([`Parse.SectionsLines`]). Nothing is assumed
--| of `spec`, so a section's characters are what `spec` is about, as in
--| [`Parse.allReads`], and its lines are those of the characters with their
--| line break ([`Text.unlinesLines`] gives them back when there is no
--| carriage return).
theorem Parse.sectionsLines ∀ (input: Text) (p: () → {Parse Char} a)
    (spec: List Char → a → Prop) (groups: NonEmptyList a)
    (h: Fail.toResult (() => Parse.all input (() => Parse.sections p)) = Ok groups)
    (reads: Parse.Reads p spec):
    Parse.SectionsLines spec groups.head groups.tail input.lines :=
  match Parse.allReads input (() => Parse.sections p) _ groups h (Parse.readsSections p spec reads) with
    | Witness read (Witness ending (Both split (Both written ended))) =>
      let lined: Text.lines input = Text.lines (MkText (read ++ ending)) :=
        Eq.cong (chars => Text.linesFrom [] [] chars) split
      rewrite lined in Parse.sectionsLinesRead spec groups read ending written ended

--| What `natDigits atLeast atMost` reads: `atLeast` to `atMost` digits, at
--| least one, and it gives their value.
def Parse.DigitsRead (atLeast atMost: Nat) (read: List Char) (n: Nat): Prop :=
  read.all Parse.isDigit = True ∧ 0 < read.length ∧ atLeast ≤ read.length ≤ atMost ∧ n = Parse.digitsValue read

theorem Parse.readsNatDigits ∀ (atLeast atMost: Nat):
    Parse.Reads (() => Parse.natDigits atLeast atMost) (Parse.DigitsRead atLeast atMost) :=
  Parse.readsWeaken
    (Parse.readsBind _ _ (read at => read = []) (start => Parse.DigitsRead atLeast atMost) Parse.readsMark (start =>
      Parse.readsWeaken
        (Parse.readsBind
          (() => Parse.span Parse.isDigit)
          (digits =>
            let count := digits.length
            if 0 < count ∧ atLeast ≤ count ≤ atMost then
              digits.map (digit => digit.digitValue.getOrElse 0) |> Nat.fromDigits
            else
              Parse.reset start
              let fewest := if atLeast == 0 then 1 else atLeast
              Parse.expected
                (if fewest == atMost then "a ${atMost}-digit number" else "a number of ${fewest} to ${atMost} digits"))
          (read taken => read = taken ∧ taken.all Parse.isDigit = True)
          (digits read n =>
            read = [] ∧ 0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost ∧ n = Parse.digitsValue digits)
          (Parse.readsSpan Parse.isDigit)
          (digits =>
            match c: ((0 < digits.length ∧ atLeast ≤ digits.length ≤ atMost): Bool) with
              | True =>
                Parse.readsWeaken
                  [p := (() => Parse.digitsValue digits)]
                  (Parse.readsPure (Parse.digitsValue digits))
                  (read n both => Both (And.left both) (Both (omega) (Both (Both (omega) (omega)) (And.right both))))
              | False => state value after honest h => Void.exfalso (Result.errNotOk h)))
        (read n h =>
          match h with
            | Witness firstRead
                (Witness nextRead (Witness digits (Both split (Both (Both same all) (Both none counted))))) =>
              rewrite split, none, List.appendNil firstRead, same in Both all counted)))
    (read n h =>
      match Parse.thenNothing (at => Parse.DigitsRead atLeast atMost) read n h with | Witness at holds => holds)

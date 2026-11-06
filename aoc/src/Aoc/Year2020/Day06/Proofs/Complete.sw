--| The converse of `Parse.sw`: input that is groups of people's lines, written
--| out as the puzzle has them, is read as those groups.
--
-- From std's lemmas on what parsers do on good input (Std/Parse/Runs.sw).

namespace Aoc.Year2020.Day06.Proofs
import Aoc.Year2020.Day06 (..)
import Std (Bool, Char, DecEq, Eq, Exists, Fail, List, NonEmptyList, Parse, Result, Set, Text, Void)

--| The rounds of a `sepBy1` after its first value, built from what `Each`
--| says was written: a separator then a value, each round reading something,
--| each value (parsed by `p`) seeing the look-ahead `valueEnd` on what follows
--| it, and the list ending where `declinesEnd` says. A std candidate (SW-1612).
theorem manyRunsOfEach (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (sepSpec: List Char → () → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: (read: List Char) → (v: a) → (after: List Char) → spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: (read: List Char) → (after: List Char) → (u: ()) → sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: (read: List Char) → (u: ()) → sepSpec read u → read ≠ [])
    (afterSeparator: (read: List Char) → (after: List Char) → (u: ()) → sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest):
    (afterFirst: List Char) → (values: List a) → Parse.Each (Parse.Then sepSpec (u => spec)) afterFirst values →
      ∃ (steps: List (List Char, a)) =>
        afterFirst = Parse.joinReads steps ∧ values = Parse.stepValues steps ∧ Parse.ManyRuns (() => Parse.sepStep p separator) steps rest
          ∧ valueEnd (afterFirst ++ rest)
  | afterFirst, [], each => Witness [] (Both each (Both rfl (Both declinesEnd (rewrite each in restEnd))))
  | afterFirst, [value, ..values], Witness stepRead (Witness remaining (Both split (Both (Witness separatorRead (Witness valueRead (Witness u (Both stepSplit (Both sepOk valueOk))))) more))) =>
    match manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty afterSeparator restEnd declinesEnd remaining values more with
      | Witness steps (Both remainingIs (Both valuesAre (Both manyRuns remainingEnd))) =>
        let laterEnd: valueEnd (Parse.joinReads steps ++ rest) := rewrite remainingIs at remainingEnd in remainingEnd
        let notEmpty: stepRead ≠ [] :=
          match separatorRead with
            | [] => Void.exfalso (separatorNotEmpty [] u sepOk rfl)
            | [char, ..others] => rewrite stepSplit in List.consNotNil char (others ++ valueRead)
        let joined: afterFirst ++ rest = separatorRead ++ (valueRead ++ (remaining ++ rest)) :=
          rewrite split, stepSplit, List.appendAssoc separatorRead valueRead remaining, List.appendAssoc separatorRead (valueRead ++ remaining) rest,
            List.appendAssoc valueRead remaining rest in rfl
        Witness [(stepRead, value), ..steps]
          (Both (rewrite split, remainingIs in rfl)
            (Both (rewrite valuesAre in rfl)
              (Both
                (Both notEmpty
                  (Both
                    (rewrite stepSplit in
                      Parse.runsSepStep p separator separatorRead valueRead (Parse.joinReads steps ++ rest) value
                        (runsSeparator separatorRead (valueRead ++ (Parse.joinReads steps ++ rest)) u sepOk)
                        (runsValue valueRead value (Parse.joinReads steps ++ rest) valueOk laterEnd))
                    manyRuns))
                (rewrite joined in afterSeparator separatorRead (valueRead ++ (remaining ++ rest)) u sepOk))))

--| `sepBy1 p separator` reads what `SepBy` says was written, given the same
--| conditions as [`manyRunsOfEach`]. A std candidate (SW-1612).
theorem runsSepBy1Of (p: () → {Parse} a) (separator: () → {Parse} ()) (spec: List Char → a → Prop) (sepSpec: List Char → () → Prop)
    (valueEnd: List Char → Prop) (rest: List Char)
    (runsValue: (read: List Char) → (v: a) → (after: List Char) → spec read v → valueEnd after → Parse.Runs p read after v)
    (runsSeparator: (read: List Char) → (after: List Char) → (u: ()) → sepSpec read u → Parse.Runs separator read after ())
    (separatorNotEmpty: (read: List Char) → (u: ()) → sepSpec read u → read ≠ [])
    (afterSeparator: (read: List Char) → (after: List Char) → (u: ()) → sepSpec read u → valueEnd (read ++ after))
    (restEnd: valueEnd rest) (declinesEnd: Parse.Declines (() => Parse.sepStep p separator) rest)
    (read: List Char) (head: a) (tail: List a) (written: Parse.SepBy spec sepSpec read (NonEmptyList.cons head tail)):
    Parse.Runs (() => Parse.sepBy1 p separator) read rest (NonEmptyList.cons head tail) :=
  match written with
    | Witness firstRead (Witness afterFirst (Witness firstValue (Both split (Both firstOk (Both isHead each))))) =>
      match manyRunsOfEach p separator spec sepSpec valueEnd rest runsValue runsSeparator separatorNotEmpty afterSeparator restEnd declinesEnd afterFirst tail each with
        | Witness steps (Both afterIs (Both tailIs (Both manyRuns firstEnd))) =>
          rewrite split, afterIs, tailIs in
            Parse.runsSepBy1 p separator firstRead head steps rest
              (runsValue firstRead head (Parse.joinReads steps ++ rest) (rewrite isHead at firstOk in firstOk) (rewrite afterIs at firstEnd in firstEnd)) manyRuns

theorem runsAsValue (p: () → {Parse} a) (read: List Char) (rest: List Char) (v: a) (w: a) (same: v = w) (runs: Parse.Runs p read rest v): Parse.Runs p read rest w :=
  rewrite same at runs in runs

--| What follows a run of letters: nothing, or something that isn't a letter.
def NoQuestionNext (rest: List Char): Prop := (char: Char) → (more: List Char) → rest = [char, ..more] → isQuestion char = False

theorem joinLetters: (letters: List Char) → Parse.joinReads (letters.map (letter => ([letter], letter))) = letters
  | [] => rfl
  | [letter, ..more] => rewrite joinLetters more in rfl

theorem valuesLetters: (letters: List Char) → Parse.stepValues (letters.map (letter => ([letter], letter))) = letters
  | [] => rfl
  | [letter, ..more] => rewrite valuesLetters more in rfl

theorem manyRunsLetters: (letters: List Char) → (rest: List Char) → letters.all isQuestion = True → NoQuestionNext rest →
    Parse.ManyRuns (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion) (letters.map (letter => ([letter], letter))) rest
  | [], [], all, stops => Parse.declinesSatisfyEnd _ _
  | [], [char, ..more], all, stops => Parse.declinesSatisfy _ _ char more (stops char more rfl)
  | [letter, ..more], rest, all, stops =>
    Both (List.consNotNil letter [])
      (Both (Parse.runsSatisfy _ _ letter (Parse.joinReads (more.map (letter2 => ([letter2], letter2))) ++ rest) (Bool.andLeft all))
        (manyRunsLetters more rest (Bool.andRight all) stops))

theorem runsPerson (read: List Char) (who: Person) (written: PersonWritten read who) (rest: List Char) (stops: NoQuestionNext rest):
    Parse.Runs person read rest who :=
  match written with
    | Both nonEmpty (Both questions same) =>
      match read with
        | [] => Void.exfalso (nonEmpty rfl)
        | [letter, ..more] =>
          let sameAnswers: [letter, ..more].toSet = who.answers :=
            Set.ext _ _ (question => Eq.trans (containsFromList [letter, ..more] question) (Eq.sym (same question)))
          let sameSet: ({ answers = [letter, ..more].toSet }: Person) = who :=
            match who with
              | { answers } => rewrite sameAnswers in rfl
          let lettersRun := Parse.runsMany1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion) [letter] letter (more.map (letter2 => ([letter2], letter2))) rest
            (Parse.runsSatisfy _ _ letter _ (Bool.andLeft questions))
            (manyRunsLetters more rest (Bool.andRight questions) stops)
          let lettersRead := rewrite joinLetters more, valuesLetters more at lettersRun in lettersRun
          runsAsValue person [letter, ..more] rest _ who sameSet
            (Parse.runsMap (() => Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)) _ ([letter] ++ more) rest
              (NonEmptyList.cons letter more) lettersRead)

--| Only line feeds and carriage returns: what `Parse.all` lets follow the last group.
def AllBreaks (rest: List Char): Prop := rest.all (char => char == '\n' ∨ char == '\r') = True

--| What follows a group: line breaks to the end of the input, or a blank line and then anything.
def Boundary (rest: List Char): Prop := AllBreaks rest ∨ ∃ (blank: List Char) => ∃ (more: List Char) => Parse.BlankLine blank ∧ rest = blank ++ more

theorem breakChar (char: Char) (isBreak: (char == '\n' ∨ char == '\r') = True): char = '\n' ∨ char = '\r' :=
  Bool.orElim isBreak (lf => Inl (DecEq.sound lf)) (cr => Inr (DecEq.sound cr))

theorem breakNotQuestion (char: Char) (isBreak: (char == '\n' ∨ char == '\r') = True): isQuestion char = False :=
  match breakChar char isBreak with
    | Inl same => rewrite same in rfl
    | Inr same => rewrite same in rfl

theorem spaceNotQuestion (char: Char) (isSpace: Parse.isSpace char = True): isQuestion char = False :=
  Bool.orElim isSpace (space => rewrite DecEq.sound space in rfl) (tab => rewrite DecEq.sound tab in rfl)

theorem lineBreakNoQuestion (lineBreak: List Char) (after: List Char) (isBreak: Parse.LineBreak lineBreak): NoQuestionNext (lineBreak ++ after) :=
  match isBreak with
    | Inl same => rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl)
    | Inr same => rewrite same in (char more found => rewrite <- List.consInjectiveHead _ _ _ _ found in rfl)

theorem allBreaksNoQuestion: (rest: List Char) → AllBreaks rest → NoQuestionNext rest
  | [], all, char, more, found => Void.exfalso (List.consNotNil char more (Eq.sym found))
  | [first, ..others], all, char, more, found =>
    rewrite <- List.consInjectiveHead _ _ _ _ found in breakNotQuestion first (Bool.andLeft all)

theorem blankNoQuestion (blank: List Char) (more: List Char) (isBlank: Parse.BlankLine blank): NoQuestionNext (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in lineBreakNoQuestion first (middle ++ (last ++ more)) firstBreak

theorem declinesLetter (rest: List Char) (stops: NoQuestionNext rest): Parse.Declines (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion) rest :=
  match rest with
    | [] => Parse.declinesSatisfyEnd _ _
    | [char, ..more] => Parse.declinesSatisfy _ _ char more (stops char more rfl)

theorem declinesPerson (rest: List Char) (stops: NoQuestionNext rest): Parse.Declines person rest :=
  Parse.declinesBind (() => Parse.many1 (() => Parse.satisfy "a question, 'a' to 'z'" isQuestion)) _ rest
    (Parse.declinesMany1 _ rest (declinesLetter rest stops))

--| A line break then a person declines when what follows is all line breaks.
theorem declinesLineAtBreaks (rest: List Char) (all: AllBreaks rest): Parse.Declines (() => Parse.sepStep person Parse.newline) rest :=
  match rest with
    | [] => Parse.declinesSepStep person Parse.newline [] (Parse.declinesNewline [] rfl rfl)
    | [char, ..more] =>
    let rest1: AllBreaks more := Bool.andRight all
    match breakChar char (Bool.andLeft all) with
      | Inl lf =>
        rewrite lf in
          Parse.declinesAfter Parse.newline (u => person()) ['\n'] more () (Parse.runsNewline ['\n'] more (Inl rfl)) (declinesPerson more (allBreaksNoQuestion more rest1))
      | Inr cr =>
        rewrite cr in
          match more with
            | [] => Parse.declinesSepStep person Parse.newline ['\r'] (Parse.declinesNewline ['\r'] rfl rfl)
            | [next, ..later] =>
              let rest2: AllBreaks later := Bool.andRight rest1
              match breakChar next (Bool.andLeft rest1) with
                | Inl lf2 =>
                  rewrite lf2 in
                    Parse.declinesAfter Parse.newline (u => person()) ['\r', '\n'] later () (Parse.runsNewline ['\r', '\n'] later (Inr rfl))
                      (declinesPerson later (allBreaksNoQuestion later rest2))
                | Inr cr2 => rewrite cr2 in Parse.declinesSepStep person Parse.newline ['\r', '\r', ..later] (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl)

--| A line break then a person declines at a blank line: the person would start at
--| the blank line's own spaces or line break.
theorem declinesLineAtBlank (blank: List Char) (more: List Char) (isBlank: Parse.BlankLine blank):
    Parse.Declines (() => Parse.sepStep person Parse.newline) (blank ++ more) :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      let after := middle ++ (last ++ more)
      let afterNoQuestion: NoQuestionNext after :=
        match middle with
          | [] => lineBreakNoQuestion last more lastBreak
          | [space, ..others] => char rest found => rewrite <- List.consInjectiveHead _ _ _ _ found in spaceNotQuestion space (Bool.andLeft spaced)
      rewrite split, List.appendAssoc first (middle ++ last) more, List.appendAssoc middle last more in
        Parse.declinesAfter Parse.newline (u => person()) first after () (Parse.runsNewline first after firstBreak) (declinesPerson after afterNoQuestion)

theorem declinesLine (rest: List Char) (boundary: Boundary rest): Parse.Declines (() => Parse.sepStep person Parse.newline) rest :=
  match boundary with
    | Inl breaks => declinesLineAtBreaks rest breaks
    | Inr (Witness blank (Witness more (Both isBlank same))) => rewrite same in declinesLineAtBlank blank more isBlank

theorem lineBreakNotEmpty (read: List Char) (u: ()) (isBreak: Parse.LineBreak read): read ≠ [] :=
  match isBreak with
    | Inl same => rewrite same in List.consNotNil '\n' []
    | Inr same => rewrite same in List.consNotNil '\r' ['\n']

theorem noQuestionOfBoundary (rest: List Char) (boundary: Boundary rest): NoQuestionNext rest :=
  match boundary with
    | Inl breaks => allBreaksNoQuestion rest breaks
    | Inr (Witness blank (Witness more (Both isBlank same))) => rewrite same in blankNoQuestion blank more isBlank

theorem runsGroup (read: List Char) (who: Group) (written: GroupWritten read who) (rest: List Char) (boundary: Boundary rest): Parse.Runs group read rest who :=
  match who, written with
    | { people }, written2 =>
      match people, written2 with
        | { head = first, tail = others }, written3 =>
        Parse.runsMap (() => Parse.lines person) (people => { people }) read rest (NonEmptyList.cons first others)
          (runsSepBy1Of person Parse.newline PersonWritten (read2 u => Parse.LineBreak read2) NoQuestionNext rest
            (read2 v after ok end => runsPerson read2 v ok after end)
            (read2 after u isBreak => Parse.runsNewline read2 after isBreak)
            lineBreakNotEmpty
            (read2 after u isBreak => lineBreakNoQuestion read2 after isBreak)
            (noQuestionOfBoundary rest boundary) (declinesLine rest boundary) read first others written3)

theorem declinesGroup (rest: List Char) (stops: NoQuestionNext rest): Parse.Declines group rest :=
  Parse.declinesBind (() => Parse.lines person) _ rest (Parse.declinesSepBy1 person Parse.newline rest (declinesPerson rest stops))

--| After a section, a blank line then a section declines when only line breaks
--| follow the first line break `first`: either the blank line isn't there, or it
-- is and no group follows it.
theorem declinesSectionAfterFirst (first: List Char) (isBreak: Parse.LineBreak first) (more: List Char) (all: AllBreaks more):
    Parse.Declines (() => Parse.sepStep group Parse.blankLine) (first ++ more) :=
  match more with
    | [] =>
      Parse.declinesSepStep group Parse.blankLine (first ++ [])
        (Parse.declinesBlankLineAfter first [] [] isBreak rfl rfl (Parse.declinesNewline [] rfl rfl))
    | [char, ..others] =>
      let others1: AllBreaks others := Bool.andRight all
      match breakChar char (Bool.andLeft all) with
        | Inl lf =>
          rewrite lf in
            rewrite <- List.appendAssoc first ['\n'] others in
              Parse.declinesAfter Parse.blankLine (u => group()) (first ++ ['\n']) others ()
                (Parse.runsBlankLine first [] ['\n'] others isBreak rfl (Inl rfl)) (declinesGroup others (allBreaksNoQuestion others others1))
        | Inr cr =>
          rewrite cr in
            match others with
              | [] =>
                Parse.declinesSepStep group Parse.blankLine (first ++ ['\r'])
                  (Parse.declinesBlankLineAfter first [] ['\r'] isBreak rfl rfl (Parse.declinesNewline ['\r'] rfl rfl))
              | [next, ..later] =>
                let later1: AllBreaks later := Bool.andRight others1
                match breakChar next (Bool.andLeft others1) with
                  | Inl lf2 =>
                    rewrite lf2 in
                      rewrite <- List.appendAssoc first ['\r', '\n'] later in
                        Parse.declinesAfter Parse.blankLine (u => group()) (first ++ ['\r', '\n']) later ()
                          (Parse.runsBlankLine first [] ['\r', '\n'] later isBreak rfl (Inr rfl)) (declinesGroup later (allBreaksNoQuestion later later1))
                  | Inr cr2 =>
                    rewrite cr2 in
                      Parse.declinesSepStep group Parse.blankLine (first ++ ['\r', '\r', ..later])
                        (Parse.declinesBlankLineAfter first [] ['\r', '\r', ..later] isBreak rfl rfl (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl))

theorem declinesSectionAtBreaks (rest: List Char) (all: AllBreaks rest): Parse.Declines (() => Parse.sepStep group Parse.blankLine) rest :=
  match rest with
    | [] => Parse.declinesSepStep group Parse.blankLine [] (Parse.declinesBlankLine [] (Parse.declinesNewline [] rfl rfl))
    | [char, ..more] =>
      let more1: AllBreaks more := Bool.andRight all
      match breakChar char (Bool.andLeft all) with
        | Inl lf => rewrite lf in declinesSectionAfterFirst ['\n'] (Inl rfl) more more1
        | Inr cr =>
          rewrite cr in
            match more with
              | [] => Parse.declinesSepStep group Parse.blankLine ['\r'] (Parse.declinesBlankLine ['\r'] (Parse.declinesNewline ['\r'] rfl rfl))
              | [next, ..later] =>
                match breakChar next (Bool.andLeft more1) with
                  | Inl lf2 => rewrite lf2 in declinesSectionAfterFirst ['\r', '\n'] (Inr rfl) later (Bool.andRight more1)
                  | Inr cr2 =>
                    rewrite cr2 in
                      Parse.declinesSepStep group Parse.blankLine ['\r', '\r', ..later] (Parse.declinesBlankLine ['\r', '\r', ..later] (Parse.declinesNewline ['\r', '\r', ..later] rfl rfl))

theorem blankLineNotEmpty (read: List Char) (u: ()) (isBlank: Parse.BlankLine read): read ≠ [] :=
  match isBlank with
    | Witness first (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
      match first, firstBreak with
        | [], Inl impossible => Void.exfalso (List.consNotNil '\n' [] (Eq.sym impossible))
        | [], Inr impossible => Void.exfalso (List.consNotNil '\r' ['\n'] (Eq.sym impossible))
        | [char, ..others], isBreak => rewrite split in List.consNotNil char (others ++ (middle ++ last))

theorem runsSections (read: List Char) (first: Group) (others: List Group) (written: Parse.SepBy GroupWritten (read2 u => Parse.BlankLine read2) read (NonEmptyList.cons first others))
    (ending: List Char) (breaks: AllBreaks ending): Parse.Runs (() => Parse.sections group) read ending (NonEmptyList.cons first others) :=
  runsSepBy1Of group Parse.blankLine GroupWritten (read2 u => Parse.BlankLine read2) Boundary ending
    (read2 v after ok end => runsGroup read2 v ok after end)
    (read2 after u isBlank =>
      match isBlank with
        | Witness first2 (Witness middle (Witness last (Both split (Both firstBreak (Both spaced lastBreak))))) =>
          rewrite split in Parse.runsBlankLine first2 middle last after firstBreak spaced lastBreak)
    blankLineNotEmpty
    (read2 after u isBlank => Inr (Witness read2 (Witness after (Both isBlank rfl))))
    (Inl breaks) (declinesSectionAtBreaks ending breaks) read first others written

--| The soundness theorem's conclusion: the input is groups written out, a
--| blank line between each two, then any line breaks.
def InputWritten (input: Text) (groups: List Group): Prop :=
  ∃ (read: List Char) => ∃ (ending: List Char) =>
    input.toList = read ++ ending
      ∧ (∃ (listed: NonEmptyList Group) => Parse.SepBy GroupWritten (read2 u => Parse.BlankLine read2) read listed ∧ groups = listed.toList)
      ∧ ending.all (char => char == '\n' ∨ char == '\r') = True

--| Input that is groups written out is read as those groups.
theorem parseComplete (input: Text) (groups: List Group) (written: InputWritten input groups): Fail.toResult (() => parseGroups input) = Ok groups :=
  match written with
    | Witness read (Witness ending (Both split (Both (Witness listed (Both listedWritten same)) breaks))) =>
      match listed, listedWritten, same with
        | { head, tail }, listedWritten2, same2 =>
          Parse.runsAll input (() => Parse.sections group |> .toList) read ending groups split breaks
            (runsAsValue (() => Parse.sections group |> .toList) read ending _ groups (Eq.sym same2)
              (Parse.runsMap (() => Parse.sections group) NonEmptyList.toList read ending (NonEmptyList.cons head tail)
                (runsSections read head tail listedWritten2 ending breaks)))

--| Soundness (`parseWritten`) is the converse: the input is written as at most one list of groups.
theorem writtenUnique (input: Text) (a: List Group) (b: List Group) (writtenA: InputWritten input a) (writtenB: InputWritten input b): a = b :=
  Result.okInjective (Eq.trans (Eq.sym (parseComplete input a writtenA)) (parseComplete input b writtenB))

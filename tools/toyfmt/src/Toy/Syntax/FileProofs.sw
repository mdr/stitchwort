--| The file from its spelling: the parser reads back what spells a
--| file's declarations (`SpelledFile`), as `linesRun` does a block's
--| statements.

namespace Toy.Syntax.Proofs
import Toy.Syntax (..)
import Std (Bool, Eq, List, NonEmptyList, Option, Parse, Text, Void)

--| The lines of a list's first group lose the blank line above them.
def firstBlankOf (isFirst: Bool) (lines: List (Spaced a)): List (Spaced a) := match isFirst with
  | True => withoutFirstBlank lines
  | False => lines

--| `tokens`, to the end of the file, spell the declarations `lines` that
--| come after the notes in `pending`, and `endTrivia` the comment lines
--| after the last: as `SpelledLines` at column 0, with a function's
--| parameters as the parameter parser reads them.
def SpelledDeclarations (isFirst: Bool) (pending lines: List (Spaced Declaration))
    (tokens: List (Parse.Located Token)) (endTrivia: List Trivia):
    Prop :=
  match lines with
    | [] => tokens = [] ∧ firstBlankOf isFirst (spacedNotes DeclarationNote endTrivia).fst = pending
    | [{ blankBefore, line = DeclarationNote comment }, ..more] =>
      SpelledDeclarations isFirst (pending ++ [{ blankBefore, line = DeclarationNote comment }]) more tokens endTrivia
    | [{ blankBefore, line = Value letComments name nameComments equalsComments inner }, ..more] =>
      ∃ (first: Parse.Located Token) => ∃ (named: Parse.Located Token) => ∃ (equals: Parse.Located Token) =>
        ∃ (bodyTokens: List (Parse.Located Token)) => ∃ (later: List (Parse.Located Token)) => tokens
          = [first, named, equals, ..bodyTokens ++ later]
          ∧ (first.value.startsLine && first.value.column == 0) = True
          ∧ first.value.kind = Reserved LetKeyword
          ∧ named.value.kind = Name name
          ∧ (InStatement 0 first.offset).allows named = True
          ∧ equals.value.kind = Sign Defines
          ∧ (InStatement 0 first.offset).allows equals = True
          ∧ letComments = (InStatement 0 first.offset).comments first
          ∧ nameComments = (InStatement 0 first.offset).comments named
          ∧ equalsComments = (InStatement 0 first.offset).comments equals
          ∧ firstBlankOf isFirst
            (notedDeclaration first.value.above (Value letComments name nameComments equalsComments inner))
            = pending ++ [{ blankBefore, line = Value letComments name nameComments equalsComments inner }]
          ∧ SpelledBody (InStatement 0 first.offset) inner bodyTokens later
          ∧ SpelledDeclarations False [] more later endTrivia
    | [
        {
          blankBefore,
          line = Function fnComments name nameComments openComments parameters closeComments equalsComments inner
        },
        ..more
      ] =>
      ∃ (first: Parse.Located Token) => ∃ (named: Parse.Located Token) => ∃ (open: Parse.Located Token) =>
        ∃ (close: Parse.Located Token) => ∃ (equals: Parse.Located Token) =>
          ∃ (parameterTokens: List (Parse.Located Token)) => ∃ (bodyTokens: List (Parse.Located Token)) =>
            ∃ (later: List (Parse.Located Token)) =>
              ∃ (listed: Option ((Text, Comments), List (Comments, (Text, Comments)))) => tokens
                = [first, named, open, ..parameterTokens ++ ([close, equals, ..bodyTokens] ++ later)]
                ∧ (first.value.startsLine && first.value.column == 0) = True
                ∧ first.value.kind = Reserved FnKeyword
                ∧ named.value.kind = Name name
                ∧ (InStatement 0 first.offset).allows named = True
                ∧ open.value.kind = Sign OpenParen
                ∧ (InStatement 0 first.offset).allows open = True
                ∧ close.value.kind = Sign CloseParen
                ∧ equals.value.kind = Sign Defines
                ∧ (InStatement 0 first.offset).allows equals = True
                ∧ Parse.Runs
                  (() => Parse.optional parameterList)
                  parameterTokens
                  ([close, equals, ..bodyTokens] ++ later)
                  listed
                ∧ parameters = parametersOf listed
                ∧ fnComments = (InStatement 0 first.offset).comments first
                ∧ nameComments = (InStatement 0 first.offset).comments named
                ∧ openComments = (InStatement 0 first.offset).comments open
                ∧ closeComments = Layout.comments InBrackets close
                ∧ equalsComments = (InStatement 0 first.offset).comments equals
                ∧ firstBlankOf isFirst
                  (notedDeclaration first.value.above
                    (Function fnComments name nameComments openComments parameters closeComments equalsComments inner))
                  = pending
                    ++ [
                      {
                        blankBefore,
                        line = Function fnComments name nameComments openComments parameters closeComments
                            equalsComments inner
                      }
                    ]
                ∧ SpelledBody (InStatement 0 first.offset) inner bodyTokens later
                ∧ SpelledDeclarations False [] more later endTrivia

--| `tokens` and `endTrivia` (both in source order) spell `file`.
def SpelledFile (file: SourceFile) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia): Prop :=
  SpelledDeclarations True [] file.declarations tokens endTrivia

theorem firstBlankOfAppend ∀ (isFirst: Bool) (group later: List (Spaced a))
    (some: group ≠ []):
    firstBlankOf isFirst (group ++ later) = firstBlankOf isFirst group ++ later :=
  match isFirst with
    | False => byComputing
    | True =>
      match group, some with
        | [], some => (some byComputing).impossible
        | [head, ..tail], some => byComputing

--| A declaration's lines are never none: they end with the declaration.
theorem groupSomeOf ∀ (isFirst: Bool) (group pending: List (Spaced a)) (last: Spaced a)
    (noted: firstBlankOf isFirst group = pending ++ [last]):
    group ≠ [] :=
  same =>
    let empty := rewrite same at noted then noted
    match isFirst, pending, empty with
      | True, [], empty => cases
      | False, [head, ..tail], empty => cases

--| A group of lines, the later groups and the notes after them, as the
--| lines after the pending ones.
theorem groupValues ∀ (isFirst: Bool)
    (group later endNotes pending more: List (Spaced Declaration)) (last: Spaced Declaration)
    (noted: firstBlankOf isFirst group = pending ++ [last])
    (values: later ++ endNotes = more):
    firstBlankOf isFirst ((group ++ later) ++ endNotes) = pending ++ [last, ..more] :=
  let assoc: (group ++ later) ++ endNotes = group ++ more :=
    Eq.trans
      (List.appendAssoc group later endNotes)
      (Eq.cong ((tail: List (Spaced Declaration)) => group ++ tail) values)
  calc firstBlankOf isFirst ((group ++ later) ++ endNotes)
    _ = firstBlankOf isFirst (group ++ more) :=
      Eq.cong ((lines: List (Spaced Declaration)) => firstBlankOf isFirst lines) assoc
    _ = firstBlankOf isFirst group ++ more :=
      firstBlankOfAppend isFirst group more (groupSomeOf isFirst group pending last noted)
    _ = (pending ++ [last]) ++ more := Eq.cong ((front: List (Spaced Declaration)) => front ++ more) noted
    _ = pending ++ [last, ..more] := List.appendAssoc pending [last] more

--| The declarations of a file read back, as the rounds of the file's
--| repetition: each round reads a declaration's tokens and gives its
--| lines, and the lines together, with the notes after the last, are the
--| file's.
theorem declarationsRun ∀ (isFirst: Bool) (pending lines: List (Spaced Declaration))
    (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (shaped: ShapedDeclarations lines)
    (spelled: SpelledDeclarations isFirst pending lines tokens endTrivia):
    ∃ (steps: List (List (Parse.Located Token), List (Spaced Declaration))) => Parse.joinReads steps = tokens
      ∧ Parse.ManyRuns declaration steps []
      ∧ firstBlankOf isFirst ((Parse.stepValues steps).concat ++ (spacedNotes DeclarationNote endTrivia).fst)
        = pending ++ lines :=
  match lines, shaped, spelled with
    | [], shaped, Both noTokens notes =>
      ([], noTokens.flipped, (declarationDeclines [] byComputing), (Eq.trans notes (List.appendNil pending).flipped))
    | [{ blankBefore, line = DeclarationNote comment }, ..more], Both lineShaped moreShaped, spelled =>
      match declarationsRun isFirst
        (pending ++ [{ blankBefore, line = DeclarationNote comment }])
        more
        tokens
        endTrivia
        moreShaped
        spelled with
        | Witness steps (Both joined (Both runs values)) => (
          steps,
          joined,
          runs,
          (Eq.trans values (List.appendAssoc pending [{ blankBefore, line = DeclarationNote comment }] more))
        )
    | [{ blankBefore, line = Value letComments name nameComments equalsComments inner }, ..more], Both innerShaped
          moreShaped, Witness first
        (Witness named
          (Witness equals
            (Witness bodyTokens
              (Witness later
                (Both split
                  (Both atMargin
                    (Both isLet
                      (Both isName
                        (Both nameAllowed
                          (Both isEquals
                            (Both equalsAllowed
                              (Both letCommented
                                (Both nameCommented
                                  (Both equalsCommented (Both noted (Both innerSpelled laterSpelled)))))))))))))))) =>
      let line := Value letComments name nameComments equalsComments inner
      match declarationsRun False [] more later endTrivia moreShaped laterSpelled with
        | Witness steps (Both joined (Both runs values)) =>
          let values2: (Parse.stepValues steps).concat ++ (spacedNotes DeclarationNote endTrivia).fst = more := values
          (
            [([first, named, equals, ..bodyTokens], notedDeclaration first.value.above line), ..steps],
            (rewrite split, joined),
            ((
              (same => cases),
              (rewrite joined, List.appendNil later, letCommented, nameCommented, equalsCommented then
                runsValueSpelled first named equals bodyTokens later name inner atMargin isLet isName nameAllowed
                    isEquals equalsAllowed innerShaped innerSpelled),
              runs
            )),
            (groupValues isFirst
              (notedDeclaration first.value.above line)
              (Parse.stepValues steps).concat
              (spacedNotes DeclarationNote endTrivia).fst
              pending
              more
              { blankBefore, line }
              noted
              values2)
          )
    | [
        {
          blankBefore,
          line = Function fnComments name nameComments openComments parameters closeComments equalsComments inner
        },
        ..more
      ], Both (Both bare innerShaped) moreShaped, Witness first
        (Witness named
          (Witness open
            (Witness close
              (Witness equals
                (Witness parameterTokens
                  (Witness bodyTokens
                    (Witness later
                      (Witness listed
                        (Both split
                          (Both atMargin
                            (Both isFn
                              (Both isName
                                (Both nameAllowed
                                  (Both opens
                                    (Both openAllowed
                                      (Both closes
                                        (Both isEquals
                                          (Both equalsAllowed
                                            (Both runsNames
                                              (Both listedSame
                                                (Both fnCommented
                                                  (Both nameCommented
                                                    (Both openCommented
                                                      (Both closeCommented
                                                        (Both equalsCommented
                                                          (Both noted
                                                            (Both innerSpelled
                                                                laterSpelled))))))))))))))))))))))))))) =>
      let line := Function fnComments name nameComments openComments parameters closeComments equalsComments inner
      match declarationsRun False [] more later endTrivia moreShaped laterSpelled with
        | Witness steps (Both joined (Both runs values)) =>
          let values2: (Parse.stepValues steps).concat ++ (spacedNotes DeclarationNote endTrivia).fst = more := values
          (
            [
              (
                [first, named, open, ..parameterTokens ++ [close, equals, ..bodyTokens]],
                notedDeclaration first.value.above line
              ),
              ..steps
            ],
            (rewrite split, joined then
              Eq.cong
                ((tail: List (Parse.Located Token)) => [first, named, open, ..tail])
                (List.appendAssoc parameterTokens [close, equals, ..bodyTokens] later)),
            ((
              (same => cases),
              (rewrite joined,
                  List.appendNil later,
                  listedSame,
                  fnCommented,
                  nameCommented,
                  openCommented,
                  closeCommented,
                  equalsCommented then
                runsFunctionSpelled first named open close equals parameterTokens bodyTokens later name listed inner
                    atMargin isFn isName nameAllowed opens openAllowed closes isEquals equalsAllowed runsNames
                    innerShaped innerSpelled),
              runs
            )),
            (groupValues isFirst
              (notedDeclaration first.value.above line)
              (Parse.stepValues steps).concat
              (spacedNotes DeclarationNote endTrivia).fst
              pending
              more
              { blankBefore, line }
              noted
              values2)
          )

--| `fileOf`, with the notes after the last declaration named.
theorem fileOfNotes ∀ (declarations: List (Spaced Declaration)) (endTrivia: List Trivia):
    fileOf declarations endTrivia
      = { declarations = withoutFirstBlank (declarations ++ (spacedNotes DeclarationNote endTrivia).fst) } :=
  match found: spacedNotes DeclarationNote endTrivia with | (endNotes, blank) => byComputing

--| The parser reads back what spells a file: on tokens and end trivia
--| that spell `file`, a file of the parser's shape, `sourceFile` reads
--| them to the end and gives `file`.
theorem runsFileSpelled ∀ (file: SourceFile) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (shaped: ShapedFile file)
    (spelled: SpelledFile file tokens endTrivia):
    Parse.Runs (() => sourceFile endTrivia) tokens [] file :=
  match file, shaped, spelled with
    | { declarations }, shaped, spelled =>
      match declarationsRun True [] declarations tokens endTrivia shaped spelled with
        | (steps, joined, runs, values) =>
          let same: fileOf (Parse.stepValues steps).concat endTrivia = { declarations } :=
            Eq.trans
              (fileOfNotes (Parse.stepValues steps).concat endTrivia)
              (Eq.cong ((lines: List (Spaced Declaration)) => ({ declarations = lines }: SourceFile)) values)
          rewrite <- joined then (rewrite <- same then runsSourceFile endTrivia steps runs)

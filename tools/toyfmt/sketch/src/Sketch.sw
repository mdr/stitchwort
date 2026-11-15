--| The rest of the direct proof of the toy formatter, top-down (SW-3418,
--| D3620): `formatDirect`, which prints the parsed tree with no check of
--| any kind, its theorems, and every lemma between them and what
--| `tools/toyfmt/src` has proved. The theorems here are proved from each
--| other, so the only gaps are the `?`s, one per open lemma; `stitchwort
--| goal` lists them and `../SKETCH.md` sizes them.
--|
--| A project of its own (`check: open-goals: warn`), so that `Toy`'s
--| `check`, `test` and `audit` don't see the open goals.

namespace Toy.Sketch
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Toy.Fmt.Proofs (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)

--| `format` without its re-parse: the source parsed and its tree
--| printed. Nothing is checked at run time.
def formatDirect (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => Refused message
  | Ok tree => Stable (tree.print width)

-- Layer E, the last of the printed tokens: their offsets.

--| Each number below the one before it: the offsets of tokens listed
--| the newest first.
def Descending: List Nat → Prop
  | [] => True
  | [only] => True
  | [newer, older, ..rest] => older < newer ∧ Descending [older, ..rest]

--| OPEN (E1). The tokens of printed pieces have growing offsets, so no
--| two share one: the parser tells a statement's first token from the
--| others by its offset (`Layout.allows`, `Layout.comments`).
theorem placedOffsets ∀ (out: List Text): Descending ((placed out).tokens.map (token => token.offset)) := ?

--| `parsedPrintViews` with the offsets: the same witnesses.
theorem parsedPrintPlaced ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    ∃ (events: List Event) => ∃ (lexemes: List (Parse.Located Lexeme)) => ∃ (tokens: List (Parse.Located Token)) =>
      ∃ (endTrivia: List Trivia) => FileEvents file events
        ∧ lex (file.print width).text = Ok { lexemes, tokens = tokens.reverse, endTrivia = endTrivia.reverse }
        ∧ tokens.map viewOf = (viewsOf events).views
        ∧ endTrivia = (viewsOf events).pending
        ∧ Descending (tokens.map (token => token.offset)) :=
  match parsedPrintTokens source file width parsed with
    | Both _ (Both _ lexed) =>
      Witness
        (eventsOf (printedPieces file.layout width).reverse)
        (Witness
          (Parse.locatedSteps 0 (stepsOnto (printedPieces file.layout width).reverse []))
          (Witness
            (placed (printedPieces file.layout width).reverse).tokens
            (Witness
              (placed (printedPieces file.layout width).reverse).pending
              (Both
                (parsedPrintEvents source file width parsed)
                (Both lexed
                  (Both
                    (Eq.cong ((seen: Views) => seen.views) (placedViews (printedPieces file.layout width).reverse))
                    (Both
                      (Eq.cong ((seen: Views) => seen.pending) (placedViews (printedPieces file.layout width).reverse))
                      (placedOffsets (printedPieces file.layout width).reverse))))))))

-- Layer D, what the parser guarantees of its trees beyond `Shaped` and
-- `Lexical`: the first-token facts.

-- `HeadedFile` and its family (`HeadedExpr`, `HeadedBody`, …) are in
-- `Toy.Fmt.Proofs` (`SpellProofs.sw`), where the spelling of expressions
-- uses them.

--| OPEN (D1). Every parsed file is `HeadedFile`: part 13's parser facts
--| (a), (b) and (c), and the blank-line fact (d) this sketch found.
theorem parseHeaded ∀ (source: Text) (file: SourceFile) (parsed: parse source = Ok file): HeadedFile file := ?

-- Layer D, the file from its spelling.

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

--| OPEN (D2). The parser reads back what spells a file: `linesRun` for
--| declarations, then `runsSourceFile`.
theorem runsFileSpelled ∀ (file: SourceFile) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (shaped: ShapedFile file)
    (spelled: SpelledFile file tokens endTrivia):
    Parse.Runs (() => sourceFile endTrivia) tokens [] file :=
  ?

-- D3 as first stated, `runsBodyNested` (`body` read with the expression
-- parser of an induction reads back a block), is proved in
-- `Toy.Syntax.Proofs` (`BlockProofs.sw`), with D4: a block also ends at
-- `then` or `else` (`BlockEnds`, `statementDeclinesEnd`). What is left of
-- D3 is the statement change itself: `Spelled`'s arm for `If` asks
-- `SpelledInline` of both branches today, and must ask `SpelledBody`
-- before E2 is true of every file; `runsIfSpelled` then calls
-- `runsBodyNested`. See SKETCH.md, "After lane 2".

-- Layer E, spelling: from the trace to the tokens the parser asks for.

--| OPEN (E2). Tokens whose views are those of a trace of the file's
--| events, with distinct offsets, spell the file.
--|
--| Proved in `Toy.Fmt.Proofs` (`SpellProofs.sw`), so no longer part of
--| what is open here: an expression's tokens from its events
--| (`exprSpells`: every form inside brackets, every form but `if`
--| outside them), a statement that is such an expression at its line
--| start (`bareSpells`), a body on its keyword's line (`inlineSpells`),
--| `else` (`reachesElse`), and the two ways a token fits its layout
--| (`innerFits`, `firstLeads`). Left: `if` outside brackets (after
--| `Spelled`'s arm for it asks `SpelledBody`), blocks and their lines
--| with the notes and blank lines above them, `let`, declarations and
--| parameters, `EndsExpression` after each expression, and this
--| statement's newest-first lists against `Rising`.
theorem spellsFile ∀ (file: SourceFile) (events: List Event)
    (tokens: List (Parse.Located Token)) (endTrivia: List Trivia)
    (shaped: ShapedFile file)
    (lexical: LexicalFile file)
    (headed: HeadedFile file)
    (laid: FileEvents file events)
    (views: tokens.map viewOf = (viewsOf events).views)
    (pending: endTrivia = (viewsOf events).pending)
    (offsets: Descending (tokens.map (token => token.offset))):
    SpelledFile file tokens.reverse endTrivia.reverse :=
  ?

-- The theorems.

--| The printed text of a parsed file parses to the same file, at every
--| width.
theorem printParses ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    parse (file.print width).text = Ok file :=
  match parsedPrintPlaced source file width parsed with
    | Witness events
        (Witness lexemes
          (Witness tokens (Witness endTrivia (Both laid (Both lexed (Both views (Both pending offsets))))))) =>
      parseReads
        (file.print width).text
        { lexemes, tokens = tokens.reverse, endTrivia = endTrivia.reverse }
        file
        lexed
        (runsFileSpelled file tokens.reverse endTrivia.reverse
          (parseShaped source file parsed)
          (spellsFile file events tokens endTrivia
            (parseShaped source file parsed)
            (parseLexical source file parsed)
            (parseHeaded source file parsed)
            laid
            views
            pending
            offsets))

--| `formatDirect` answers every source that parses, with its tree
--| printed; it refuses only what the parser refuses.
theorem formatDirectAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    formatDirect source width = Stable (tree.print width) :=
  rewrite parsed in rfl

--| Round trip: the output of `formatDirect` parses to the source's tree.
theorem formatDirectRoundTrip ∀ (source: Text) (width: Nat) (output: Printed)
    (h: formatDirect source width = Stable output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.print width ∧ parse output.text = Ok tree :=
  match e: parse source with
    | Ok tree =>
      let same := stableInjective (tree.print width) output h
      Witness tree (Both rfl (Both (Eq.sym same) (rewrite <- same in printParses source tree width e)))

--| Idempotence: formatting the output again, at the same width, gives
--| the output.
theorem formatDirectIdempotent ∀ (source: Text) (width: Nat) (output: Printed)
    (h: formatDirect source width = Stable output):
    formatDirect output.text width = Stable output :=
  match formatDirectRoundTrip source width output h with
    | Witness tree (Both parsed (Both same reparsed)) =>
      rewrite same in formatDirectAnswers (tree.print width).text width tree (rewrite <- same in reparsed)

--| `format`'s check never fails: it answers what `formatDirect` does, on
--| every source at every width, so `format`'s theorems (`Toy.Fmt.Proofs`:
--| the round trip, idempotence and the file loop's) are `formatDirect`'s.
theorem formatAgrees ∀ (source: Text) (width: Nat): format source width = formatDirect source width :=
  match e: parse source with
    | Err message => rfl
    | Ok tree =>
      match c: parse (tree.print width).text == Ok tree with
        | True => rfl
        | False => Void.exfalso (DecEq.soundFalse _ _ c (printParses source tree width e))

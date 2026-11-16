--| The rest of the direct proof of the toy formatter, top-down (SW-3418,
--| D3620): `formatDirect`, which prints the parsed tree with no check of
--| any kind, its theorems, and every lemma between them and what
--| `tools/toyfmt/src` has proved. The theorems here are proved from each
--| other, and every lemma they need is now proved in `src/`, so there are no
--| `?`s left; `../SKETCH.md` has the history.
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

-- Layer E, the last of the printed tokens: their offsets. E1 is proved:
-- `placedOffsets` (`Toy.Fmt.Proofs`, `PlaceProofs.sw`) says the tokens of
-- printed pieces have falling offsets (`Descending`), so no two share
-- one.

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

-- D1 is proved: `parseHeaded` (`Toy.Fmt.Proofs`, `HeadProofs.sw`) says
-- every parsed file is `HeadedFile`: part 13's parser facts (a), (b) and
-- (c), and the blank-line fact (d) this sketch found. `bareStatement`
-- clears the comments above its expression's first token outside
-- brackets (`Layout.headed`), so (a) and (b) are facts about the tree it
-- built. See SKETCH.md, "After lane 3".

-- Layer D, the file from its spelling.

-- D2 is proved: `runsFileSpelled` (`Toy.Syntax.Proofs`, `FileProofs.sw`,
-- with `SpelledFile` and `SpelledDeclarations`) says the parser reads
-- back what spells a file: `declarationsRun` for the declarations, then
-- `runsSourceFile`.

-- D3 and D4 are proved in `Toy.Syntax.Proofs` (`BlockProofs.sw`), with
-- the statement change they needed: `Spelled`'s arm for `If` asks
-- `SpelledBody` of each branch, before whatever may follow it (`After`);
-- `runsIfSpelled` reads a block branch back by `runsBodyNested`; and a
-- block also ends at `then` or `else` (`BlockEnds`,
-- `statementDeclinesEnd`). `runsIfBlockExample` is an instance. See
-- SKETCH.md, "After lane 2".

-- Layer E, spelling: from the trace to the tokens the parser asks for.

-- E2 is proved: `spellsFile` (`Toy.Fmt.Proofs`, `BlockSpellProofs.sw`)
-- says tokens whose views are those of a trace of the file's events,
-- with falling offsets, spell the file: `exprSpells` for expressions,
-- `exprOut`, `bodyOut` and `linesOut` for an `if` outside brackets, bodies
-- and blocks, `declarationsOut` for the declarations. Nothing is open
-- here now.

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

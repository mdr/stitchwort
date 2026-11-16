--| The formatter with no check at run time (SW-3418): `formatDirect`
--| parses and prints, and here is why that is enough. The printed text
--| of a parsed file parses to the same file (`printParses`), from the
--| chain the other files of this namespace prove: the printed pieces lex
--| to tokens whose views are those of the file's events
--| (`parsedPrintTokens`), with falling offsets (`placedOffsets`); such
--| tokens spell the file (`spellsFile`); and the parser reads back what
--| spells a file (`runsFileSpelled`). So `formatDirect` keeps the tree
--| (`formatDirectRoundTrip`), formats its own output to itself
--| (`formatDirectIdempotent`), and answers what the checked `format`
--| does (`formatAgrees`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)

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
--| every source at every width.
theorem formatAgrees ∀ (source: Text) (width: Nat): format source width = formatDirect source width :=
  match e: parse source with
    | Err message => rfl
    | Ok tree =>
      match c: parse (tree.print width).text == Ok tree with
        | True => rfl
        | False => Void.exfalso (DecEq.soundFalse _ _ c (printParses source tree width e))

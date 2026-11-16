--| Why `format` keeps the tree. It parses and prints, and the printed
--| text of a parsed file parses to the same file (`printParses`), from the
--| chain the other files of this namespace prove: the printed pieces lex
--| to tokens whose views are those of the file's events
--| (`parsedPrintTokens`), with falling offsets (`placedOffsets`); such
--| tokens spell the file (`spellsFile`); and the parser reads back what
--| spells a file (`runsFileSpelled`). So `format` keeps the tree
--| (`formatRoundTrip`) and formats its own output to itself
--| (`formatIdempotent`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, Nat, Option, Parse, Result, Text)

--| `parsedPrintViews` with the offsets: the same witnesses.
theorem parsedPrintPlaced ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    ∃ (events: List Event) => ∃ (lexemes: List (Parse.Located Lexeme)) => ∃ (tokens: List (Parse.Located Token)) =>
      ∃ (endTrivia: List Trivia) => FileEvents file events
        ∧ lex (file.print width) = Ok { lexemes, tokens = tokens.reverse, endTrivia = endTrivia.reverse }
        ∧ tokens.map viewOf = (viewsOf events).views
        ∧ endTrivia = (viewsOf events).pending
        ∧ Descending (tokens.map (token => token.offset)) :=
  match parsedPrintTokens source file width parsed with
    | (_, _, lexed) => (
      (eventsOf (printedPieces file.layout width).reverse),
      (Parse.locatedSteps 0 (stepsOnto (printedPieces file.layout width).reverse [])),
      (placed (printedPieces file.layout width).reverse).tokens,
      (placed (printedPieces file.layout width).reverse).pending,
      (parsedPrintEvents source file width parsed),
      lexed,
      (Eq.cong ((seen: Views) => seen.views) (placedViews (printedPieces file.layout width).reverse)),
      (Eq.cong ((seen: Views) => seen.pending) (placedViews (printedPieces file.layout width).reverse)),
      (placedOffsets (printedPieces file.layout width).reverse)
    )

--| The printed text of a parsed file parses to the same file, at every
--| width.
theorem printParses ∀ (source: Text) (file: SourceFile) (width: Nat)
    (parsed: parse source = Ok file):
    parse (file.print width) = Ok file :=
  match parsedPrintPlaced source file width parsed with
    | (events, lexemes, tokens, endTrivia, laid, lexed, views, pending, offsets) =>
      parseReads
        (file.print width)
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

--| `format` answers every source that parses, with its tree printed; it
--| refuses only what the parser refuses.
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    format source width = Formatted (tree.print width) :=
  rewrite parsed in rfl

--| Round trip: the output of `format` parses to the source's tree.
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.print width ∧ parse output = Ok tree :=
  match e: parse source with
    | Ok tree =>
      let same := formattedInjective (tree.print width) output h
      (tree, rfl, (Eq.sym same), (rewrite <- same in printParses source tree width e))

--| Idempotence: formatting the output again, at the same width, gives
--| the output.
theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output :=
  match formatRoundTrip source width output h with
    | (tree, parsed, same, reparsed) =>
      rewrite same in formatAnswers (tree.print width) width tree (rewrite <- same in reparsed)

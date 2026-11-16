--| Why `format` keeps the tree. It parses and prints, and the printed
--| text of a parsed file parses to the same file (`printParses`), from the
--| chain the other files of this namespace prove: the printed pieces lex
--| to tokens whose views are those of the printed trace
--| (`printedTokens`), with falling offsets (`placedOffsets`); rule N
--| takes them to tokens with the views of the file's events
--| (`settledViews`), since the printed trace is the file's events but for
--| each trailing comment coming after the closers on its line; such
--| tokens spell the file (`spellsFile`); and the parser reads back what
--| spells a file (`runsFileSpelled`). So `format` keeps the tree
--| (`formatRoundTrip`) and formats its own output to itself
--| (`formatIdempotent`). Two sources with one tree format alike
--| (`formatSameTree`), and what doesn't parse is refused with the parser's
--| message (`formatRefuses`).

namespace Toy.Fmt.Proofs
import Toy.Doc (..)
import Toy.Doc.Proofs (..)
import Toy.Syntax (..)
import Toy.Syntax.Proofs (..)
import Toy.Fmt (..)
import Std (Bool, Eq, List, Nat, Option, Parse, Result, Text)

--| The printed pieces lex to the tokens, whose views are those of the
--| printed trace, with the offsets falling; and the file's events
--| (`printedEvents`) are a trace the printed one is, but for each
--| trailing comment coming after the closers on its line: the same
--| witnesses, for any tree with the parser's guarantees.
theorem printedPlaced ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file):
    ∃ (laid: List Event) => ∃ (printed: List Event) => ∃ (lexemes: List (Parse.Located Lexeme)) =>
      ∃ (tokens: List (Parse.Located Token)) => ∃ (endTrivia: List Trivia) => FileEvents file laid
        ∧ Tucks laid printed
        ∧ lex (file.print width) = Ok { lexemes, tokens = tokens.reverse, endTrivia = endTrivia.reverse }
        ∧ tokens.map viewOf = (viewsOf printed).views
        ∧ endTrivia = (viewsOf printed).pending
        ∧ Descending (tokens.map (token => token.offset)) :=
  match printedTokens file width parsed.right.left, printedEvents file width parsed.right.left with
    | (_, lexed), (laid, events, tucks) => (
      laid,
      (eventsOf (printedPieces file.layout width).reverse),
      (Parse.locatedSteps 0 (stepsOnto (printedPieces file.layout width).reverse [])),
      (placed (printedPieces file.layout width).reverse).tokens,
      (placed (printedPieces file.layout width).reverse).pending,
      events,
      tucks,
      lexed,
      (Eq.cong ((seen: Views) => seen.views) (placedViews (printedPieces file.layout width).reverse)),
      (Eq.cong ((seen: Views) => seen.pending) (placedViews (printedPieces file.layout width).reverse)),
      (placedOffsets (printedPieces file.layout width).reverse)
    )

--| What the parser reads of a printed file, once rule N has been through
--| its tokens: tokens with the views of the file's events, in the tree's
--| order. The lexer puts a comment printed after closers on the last of
--| them; rule N's first half takes it back to the token the tree has it
--| on (`tucksHome`), and its second half finds no comma holding
--| anything. The offsets are the printed tokens'.
theorem settledViews ∀ (file: SourceFile) (width: Nat)
    (parsed: Parsed file):
    ∃ (events: List Event) => ∃ (lexed: Lexed) => ∃ (tokens: List (Parse.Located Token)) =>
      ∃ (endTrivia: List Trivia) => FileEvents file events
        ∧ lex (file.print width) = Ok lexed
        ∧ lexed.settled.tokens = tokens.reverse
        ∧ lexed.settled.endTrivia = endTrivia.reverse
        ∧ tokens.map viewOf = (viewsOf events).views
        ∧ endTrivia = (viewsOf events).pending
        ∧ Descending (tokens.map (token => token.offset)) :=
  match printedPlaced file width parsed with
    | (laid, printed, lexemes, tokens, endTrivia, events, tucks, lexed, views, pending, offsets) =>
      match fileCalm file laid parsed.left parsed.right.left events with
        | (after, calms) =>
          let found: Lexed := { lexemes, tokens = tokens.reverse, endTrivia = endTrivia.reverse }
          let homed := tokens.reverse.foldLeft [] homeStep
          let home := tucksHome laid printed after tucks calms
          let homedViews: homed.map viewOf = (viewsOf laid).views := calc homed.map viewOf
            _ = homeViews (tokens.map viewOf) := tokensHomeViews tokens
            _ = homeViews (viewsOf printed).views := Eq.cong homeViews views
            _ = (viewsOf laid).views := home.left
          let stable: StableViews (homed.map viewOf) := rewrite homedViews then home.right.right
          let steady := stableTokens homed stable
          let same := settledHomed found tokens byComputing steady.right
          let sameOffsets: homed.map (token => token.offset) = tokens.map (token => token.offset) := calc homed.map
            (token => token.offset)
            _ = tokens.reverse.reverse.map (token => token.offset) ++ [] :=
              homeFoldSame (each => each.offset) (each trailing => byComputing) tokens.reverse []
            _ = tokens.reverse.reverse.map (token => token.offset) :=
              List.appendNil (tokens.reverse.reverse.map (token => token.offset))
            _ = tokens.map (token => token.offset) :=
              Eq.cong
                ((found: List (Parse.Located Token)) => found.map (token => token.offset))
                (List.reverseReverse tokens)
          (
            laid,
            found,
            homed,
            endTrivia,
            events,
            lexed,
            same.left,
            same.right,
            homedViews,
            (Eq.trans pending home.right.left),
            (rewrite sameOffsets then offsets)
          )

--| The printed text of a tree with the parser's guarantees parses to the
--| same tree, at every width. No source is mentioned: a tree a pass built
--| qualifies as well as one the parser read.
theorem printParses ∀ (file: SourceFile) (width: Nat) (parsed: Parsed file): parse (file.print width) = Ok file :=
  match settledViews file width parsed with
    | (events, lexed, tokens, endTrivia, laid, lexes, sameTokens, sameTrivia, views, pending, offsets) =>
      parseReads
        (file.print width)
        lexed
        file
        lexes
        (rewrite sameTokens, sameTrivia then
          runsFileSpelled file tokens.reverse endTrivia.reverse parsed.left
            (spellsFile file events tokens endTrivia parsed.left parsed.right.left parsed.right.right laid views pending
                offsets))

--| `format` answers every source that parses, with its tree printed; it
--| refuses only what the parser refuses.
theorem formatAnswers ∀ (source: Text) (width: Nat) (tree: SourceFile)
    (parsed: parse source = Ok tree):
    format source width = Formatted (tree.print width) :=
  rewrite parsed

--| Round trip: the output of `format` parses to the source's tree.
theorem formatRoundTrip ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    ∃ (tree: SourceFile) => parse source = Ok tree ∧ output = tree.print width ∧ parse output = Ok tree :=
  match e: parse source with
    | Ok tree =>
      let same := formattedInjective (tree.print width) output h
      (tree, byComputing, same.flipped, (rewrite <- same then printParses tree width (parseParsed source tree e)))

--| Idempotence: formatting the output again, at the same width, gives
--| the output.
theorem formatIdempotent ∀ (source: Text) (width: Nat) (output: Text)
    (h: format source width = Formatted output):
    format output width = Formatted output :=
  match formatRoundTrip source width output h with
    | (tree, parsed, same, reparsed) =>
      rewrite same then formatAnswers (tree.print width) width tree (rewrite <- same then reparsed)

--| The output depends on the source only through its tree: two sources
--| that parse to the same tree format to the same text, however each was
--| laid out. A formatter that gave its input back would fail this on any
--| two layouts of one tree (`Toy.Fmt.Degenerate`).
theorem formatSameTree ∀ (first second: Text) (width: Nat) (tree: SourceFile)
    (parsesFirst: parse first = Ok tree)
    (parsesSecond: parse second = Ok tree):
    format first width = format second width :=
  rewrite formatAnswers first width tree parsesFirst, formatAnswers second width tree parsesSecond

--| A source that doesn't parse (or doesn't lex) is not formatted: the
--| answer is `ParseError` with the parser's message, at every width.
theorem formatRefuses ∀ (source: Text) (width: Nat) (message: Text)
    (refused: parse source = Err message):
    format source width = ParseError message :=
  rewrite refused

--| `format` refuses nothing else: a `ParseError` is the parser's own, with
--| its message.
theorem formatRefusesOnly ∀ (source: Text) (width: Nat) (message: Text)
    (refused: format source width = ParseError message):
    parse source = Err message :=
  match e: parse source with | Err found => rewrite parseErrorInjective found message refused

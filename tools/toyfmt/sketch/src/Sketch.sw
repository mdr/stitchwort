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

--| A list of lines as `withoutFirstBlank` leaves it: no blank line is
--| kept above the first.
def Unspaced (lines: List (Spaced a)): Prop := withoutFirstBlank lines = lines

--| A body that is one expression.
def OneExpression: List (Spaced Statement) → Prop
  | [{ line = Bare _, .. }] => True
  | _ => False

--| What the parser guarantees of where comments and blocks are, in an
--| expression read inside brackets (`bracketed`) or in a statement:
--| outside brackets a statement's first token holds no comments above it
--| (they are the block's comment lines), nor does the first token of a
--| body on its keyword's line (it doesn't start a line); inside
--| brackets every body is one expression; and no body keeps a blank line
--| above its first line.
def Headed (bracketed: Bool): Expr → Prop
  | Var _ _ => True
  | NumberLiteral _ _ => True
  | StringLiteral _ _ => True
  | Bracketed _ inner _ => Headed True inner
  | ListLiteral _ items _ => HeadedItems items
  | Call callee _ arguments _ => Headed bracketed callee ∧ HeadedItems arguments
  | Field target _ _ _ => Headed bracketed target
  | Negate _ operand => Headed bracketed operand
  | Binary _ _ left right => Headed bracketed left ∧ Headed bracketed right
  | If _ condition _ whenTrue _ whenFalse =>
    Headed bracketed condition ∧ HeadedBody bracketed whenTrue ∧ HeadedBody bracketed whenFalse

def HeadedItems: List Item → Prop
  | [] => True
  | [{ value, .. }, ..rest] => Headed True value ∧ HeadedItems rest

def HeadedBody (bracketed: Bool): Body → Prop
  | { statements } =>
    HeadedLines bracketed statements ∧ Unspaced statements ∧ (bracketed = True → OneExpression statements)

def HeadedLines (bracketed: Bool): List (Spaced Statement) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => HeadedStatement bracketed line ∧ HeadedLines bracketed rest

def HeadedStatement (bracketed: Bool): Statement → Prop
  | Let letComments _ _ _ body => letComments.above = [] ∧ HeadedBody False body
  | Bare value => (bracketed = False → value.firstAbove = []) ∧ Headed bracketed value
  | StatementNote _ => True

def HeadedDeclaration: Declaration → Prop
  | Function fnComments _ _ _ _ _ _ body => fnComments.above = [] ∧ HeadedBody False body
  | Value letComments _ _ _ body => letComments.above = [] ∧ HeadedBody False body
  | DeclarationNote _ => True

def HeadedDeclarations: List (Spaced Declaration) → Prop
  | [] => True
  | [{ line, .. }, ..rest] => HeadedDeclaration line ∧ HeadedDeclarations rest

def HeadedFile: SourceFile → Prop
  | { declarations } => HeadedDeclarations declarations ∧ Unspaced declarations

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

--| OPEN (D3). `body` read with the expression parser of an induction
--| (`self`, under `ReadsNested`) reads back what spells a body, a block
--| too: what `runsIfSpelled` needs for an `if` whose branch is a block.
--| Not used by the theorems below as it stands: `Spelled`'s arm for `If`
--| asks `SpelledInline` of both branches today, and must ask
--| `SpelledBody` (the two become mutual) before E2 is true of every
--| file. See SKETCH.md, "Statements that must change".
theorem runsBodyNested ∀ (self: Layout → {Parse (Parse.Located Token)} Expr) (layout: Layout) (bound: Nat)
    (nested: ReadsNested self bound)
    (found: Body) (tokens rest: List (Parse.Located Token))
    (shaped: ShapedBody found)
    (spelled: SpelledBody layout found tokens rest)
    (short: tokens.length < bound):
    Parse.Runs (() => body self layout) tokens rest found :=
  ?

-- Layer E, spelling: from the trace to the tokens the parser asks for.

--| OPEN (E2). Tokens whose views are those of a trace of the file's
--| events, with distinct offsets, spell the file.
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

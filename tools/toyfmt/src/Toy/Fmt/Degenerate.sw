--| Formatters nobody wants, each shown to break one of `format`'s
--| theorems by a computed example. A theorem that no formatter could fail
--| says nothing, so each statement here is restated for any formatter
--| (`SameTree`, `KeepsComments`, `RoundTrips`), and a degenerate formatter
--| is refuted on one small source. `format` has all three by the theorems
--| of those names.
--|
--| The last part shows the tree telling files apart: sources that differ
--| in a comment, a blank line, an operator or the order of two
--| declarations have different trees, and two layouts of one program have
--| the same tree.

namespace Toy.Fmt.Degenerate
import Toy.Fmt (..)
import Toy.Fmt.KeepsComments (formatKeepsComments)
import Toy.Fmt.Proofs (..)
import Toy.Syntax (..)
import Std (Bool, DecEq, Eq, List, Nat, Option, Parse, Result, Text, Void)

--| What `format` is: a source and a width to an answer.
type Formatter = Text → Nat → FormatResult

-- The theorems, for any formatter.

--| `formatSameTree`'s statement.
def SameTree (formatter: Formatter): Prop :=
  ∀ (first second: Text) (width: Nat) (tree: SourceFile) (parsesFirst: parse first = Ok tree) (parsesSecond: parse
      second
    = Ok tree) => formatter first width = formatter second width

--| `formatKeepsComments`'s statement.
def KeepsComments (formatter: Formatter): Prop :=
  ∀ (source output: Text) (width: Nat) (before after: Lexed) (formats: formatter source width
    = Formatted output) (lexedBefore: lex source = Ok before) (lexedAfter: lex output = Ok after) => after.comments
    = before.comments

--| `formatRoundTrip`'s statement, without the part that names the printer:
--| the output parses to the source's tree.
def RoundTrips (formatter: Formatter): Prop :=
  ∀ (source: Text) (width: Nat) (output: Text) (formats: formatter source width
    = Formatted output) => ∃ (tree: SourceFile) => parse source = Ok tree ∧ parse output = Ok tree

theorem formatHasSameTree: SameTree format := formatSameTree

theorem formatHasKeepsComments: KeepsComments format := formatKeepsComments

theorem formatRoundTrips: RoundTrips format := source width output formats =>
  match formatRoundTrip source width output formats with | (tree, parsed, same, reparsed) => (tree, parsed, reparsed)

-- The identity formatter.

--| Gives back whatever parses, as written.
def identity (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => ParseError message
  | Ok _ => Formatted source

--| The identity formatter breaks `formatSameTree`: two layouts of `let x =
--| 1` have one tree and come back different.
theorem identityNotSameTree ∀ (holds: SameTree identity): Void :=
  let spaced := "let  x  =  1\n"
  let tight := "let x = 1\n"
  let tree: SourceFile := {
    declarations = [
      {
        blankBefore = False,
        line = Value Comments.none "x" Comments.none Comments.none {
          statements = [{ blankBefore = False, line = Bare (NumberLiteral "1" Comments.none) }]
        }
      }
    ]
  }
  let same: identity spaced 80 = identity tight 80 := holds spaced tight 80 tree byComputing byComputing
  let differ: (identity spaced 80 == identity tight 80) = False := byComputing
  (DecEq.soundFalse _ _ differ same).impossible

-- The formatter that deletes comments.

--| The source without its comment lexemes.
def withoutComments (source: Text): Text := match lex source with
  | Err _ => source
  | Ok lexed =>
    lexed.lexemes.filter (lexeme =>
      not
        (lexeme.value
          |> matches
            | CommentLexeme))
      |> .map (lexeme => cut source lexeme)
      |> Text.concat

--| `format`, on the source with its comments deleted.
def deleteComments (source: Text) (width: Nat): FormatResult := format (withoutComments source) width

--| What `lex` answered for `source`; nothing, for a source it refused.
def lexed (source: Text): Lexed := match lex source with
  | Ok found => found
  | Err _ => { lexemes = [], tokens = [], endTrivia = [] }

--| The formatter that deletes comments breaks `formatKeepsComments`: the
--| source has `-- one` and the output has none.
theorem deleteCommentsLosesOne ∀ (holds: KeepsComments deleteComments): Void :=
  let source := "let x = 1 -- one\n"
  let output := "let x = 1\n"
  let same: (lexed output).comments = (lexed source).comments :=
    holds source output 80 (lexed source) (lexed output) byComputing byComputing byComputing
  let differ: ((lexed output).comments == (lexed source).comments) = False := byComputing
  (DecEq.soundFalse _ _ differ same).impossible

-- The one-line formatter.

--| A result that isn't `Ok` is no `Ok value`.
theorem notOk ∀ (result: Result SourceFile Text) (tree: SourceFile)
    (failed: result.isOk = False)
    (ok: result = Ok tree):
    Void :=
  match result, failed, ok with | Err message, _, clash => cases

--| `format`'s output with every line break but the last made a space.
def oneLine (source: Text) (width: Nat): FormatResult := match format source width with
  | ParseError message => ParseError message
  | Formatted text => Formatted (Text.joinWith text.lines " " ++ "\n")

--| The one-line formatter breaks `formatRoundTrip`: two declarations on
--| one line don't parse.
theorem oneLineDoesNotParse ∀ (holds: RoundTrips oneLine): Void :=
  match holds "let x = 1\nlet y = 2\n" 80 "let x = 1 let y = 2\n" byComputing with
    | (tree, parsed, reparsed) => notOk (parse "let x = 1 let y = 2\n") tree byComputing reparsed

-- The tree tells files apart.

def sameTree (first second: Text): Bool := parse first == parse second

theorem layoutSame: sameTree "let x = f(1, 2)\n" "let x =\n  f(1,\n    2)\n" = True := byComputing

theorem commentDiffers: sameTree "let x = 1 -- one\n" "let x = 1\n" = False := byComputing

theorem commentTextDiffers: sameTree "let x = 1 -- one\n" "let x = 1 -- two\n" = False := byComputing

theorem commentPlaceDiffers: sameTree "let x = f(1, -- c\n  2)\n" "let x = f(1,\n  2) -- c\n" = False := byComputing

theorem blankLineDiffers: sameTree "let x = 1\n\nlet y = 2\n" "let x = 1\nlet y = 2\n" = False := byComputing

theorem operatorDiffers: sameTree "let x = a + b\n" "let x = a - b\n" = False := byComputing

theorem orderDiffers: sameTree "let x = 1\nlet y = 2\n" "let y = 2\nlet x = 1\n" = False := byComputing

theorem bracketsDiffer: sameTree "let x = (a + b) + c\n" "let x = a + b + c\n" = False := byComputing

theorem stringDiffers: sameTree "let x = \"a b\"\n" "let x = \"a  b\"\n" = False := byComputing

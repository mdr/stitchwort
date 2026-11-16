--| `formatKeepsComments` on today's toy (D3663, stage T1b): stated, and
--| proved from one open lemma, `parseCarries`, the parser's half. It is
--| here and not in `Toy.Fmt.Proofs` because that lemma is open
--| (SKETCH-PLUS.md, "T1b").
--|
--| The statement is between two texts and reads them with `lex` and
--| `Lexed.comments` only. The tree's comments (`SourceFile.comments`) are
--| the proof's middle term and appear in no statement about `format`.

namespace Toy.Fmt.KeepsComments
import Toy.Fmt (..)
import Toy.Fmt.Proofs (..)
import Toy.Syntax (..)
import Std (Bool, List, Nat, Option, Result, Text)

-- The comments a tree holds, token by token in source order.

def Comments.all (comments: Comments): List Comment := comments.above ++ comments.after.toList

def Expr.comments: Expr → List Comment
  | Var _ comments => comments.all
  | NumberLiteral _ comments => comments.all
  | StringLiteral _ comments => comments.all
  | Bracketed open inner close => open.all ++ inner.comments ++ close.all
  | ListLiteral open items close => open.all ++ itemsComments items ++ close.all
  | Call callee open arguments close => callee.comments ++ open.all ++ itemsComments arguments ++ close.all
  | Field target dot _ nameComments => target.comments ++ dot.all ++ nameComments.all
  | Negate minus operand => minus.all ++ operand.comments
  | Binary _ sign left right => left.comments ++ sign.all ++ right.comments
  | If ifComments condition thenComments whenTrue elseComments whenFalse =>
    ifComments.all
      ++ condition.comments
      ++ thenComments.all
      ++ whenTrue.comments
      ++ elseComments.all
      ++ whenFalse.comments

def itemsComments: List Item → List Comment
  | [] => []
  | [{ value, comma }, ..rest] => value.comments ++ comma.all ++ itemsComments rest

def Body.comments: Body → List Comment
  | { statements } => linesComments statements

def linesComments: List (Spaced Statement) → List Comment
  | [] => []
  | [{ blankBefore, line }, ..rest] => line.comments ++ linesComments rest

def Statement.comments: Statement → List Comment
  | Let letComments _ nameComments equals body => letComments.all ++ nameComments.all ++ equals.all ++ body.comments
  | Bare value => value.comments
  | StatementNote comment => [comment]

def Parameter.allComments (parameter: Parameter): List Comment := parameter.comments.all ++ parameter.comma.all

def Declaration.comments: Declaration → List Comment
  | Function fnComments _ nameComments open parameters close equals body =>
    fnComments.all
      ++ nameComments.all
      ++ open.all
      ++ parameters.flatMap Parameter.allComments
      ++ close.all
      ++ equals.all
      ++ body.comments
  | Value letComments _ nameComments equals body => letComments.all ++ nameComments.all ++ equals.all ++ body.comments
  | DeclarationNote comment => [comment]

def SourceFile.comments (file: SourceFile): List Comment := file.declarations.flatMap (spaced => spaced.line.comments)

--| The parser's half: the tree holds exactly the comments the lexer
--| found, in the same order. Open; SKETCH-PLUS.md ("T1b") says what its
--| proof needs.
theorem parseCarries ∀ (source: Text) (lexed: Lexed) (tree: SourceFile)
    (lexes: lex source = Ok lexed)
    (parsed: parse source = Ok tree):
    tree.comments = lexed.comments :=
  ?

--| Formatting keeps every comment, with the same text and in the same
--| order: the comments the lexer finds in the output are those it finds
--| in the source. Neither side goes through the parser, the tree or the
--| printer, so a parser that dropped a comment would break this, where it
--| would break no statement that compares two trees.
theorem formatKeepsComments ∀ (source output: Text) (width: Nat) (before after: Lexed)
    (formats: format source width = Formatted output)
    (lexedBefore: lex source = Ok before)
    (lexedAfter: lex output = Ok after):
    after.comments = before.comments :=
  match formatRoundTrip source width output formats with
    | (tree, parsed, same, reparsed) =>
      calc after.comments
        _ = tree.comments := (parseCarries output after tree lexedAfter reparsed).flipped
        _ = before.comments := parseCarries source before tree lexedBefore parsed

-- Both statements on sources with a comment in each kind of place.

--| Whether `source`'s tree holds the lexer's comments (`parseCarries`).
def carried (source: Text): Bool := carriedBy (lex source) (parse source)

def carriedBy (lexed: Result Lexed Text) (parsed: Result SourceFile Text): Bool := match lexed, parsed with
  | Ok found, Ok tree => tree.comments == found.comments
  | _, _ => False

--| How many comments `source` has, if formatting it at `width` keeps them
--| all in order (`formatKeepsComments`).
def kept (source: Text) (width: Nat): Option Nat := match format source width with
  | Formatted output => keptBetween (lex source) (lex output)
  | ParseError _ => None

def keptBetween (before after: Result Lexed Text): Option Nat := match before, after with
  | Ok source, Ok output => if output.comments == source.comments then Some source.comments.length else None
  | _, _ => None

--| Above a declaration, after its tokens, above and after a statement, and
--| at the end of the file.
def inBlocks: Text := "-- top\n\nfn f(a, b) = -- eq\n  -- note\n  let c = a -- a\n\n  -- last\n  c + b -- sum\n-- end\n"

--| Inside brackets, where own-line comments stay on the token below, and
--| after closers and commas.
def inBrackets: Text := "let x = f( -- open\n  -- above a\n  a, -- comma\n  [b -- b\n  ] -- close\n) -- call\n"

--| On continuation lines of a statement: above an operator, above `then`
--| and `else`, and above a body's first statement.
def onContinuations: Text :=
  "fn g(a) =\n  if a -- cond\n    -- above then\n    then\n      -- above one\n      1\n  -- above else\n  else a\n    -- above plus\n    + 2 -- two\n"

theorem carriedInBlocks: carried inBlocks = True := byComputing

theorem carriedInBrackets: carried inBrackets = True := byComputing

theorem carriedOnContinuations: carried onContinuations = True := byComputing

theorem keptInBlocks: kept inBlocks 80 = Some 7 := byComputing

theorem keptInBrackets: kept inBrackets 80 = Some 6 := byComputing

theorem keptNarrow: kept inBrackets 10 = Some 6 := byComputing

theorem keptOnContinuations: kept onContinuations 80 = Some 6 := byComputing

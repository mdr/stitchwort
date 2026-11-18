--| Slice 1 of the proved formatter (docs/proposals/
--| self-hosted-fmt-proof-plan.md §1.1, §1.2): files of `def name: T := e`
--| whose types and bodies are names, numerals, brackets, tuples, lists,
--| applications, binary operators, `-`, `!` and `→`, with comments
--| anywhere.
--|
--| The slice is a test on the real tree, `within1`, so every theorem is
--| about the real parser and printer with one more hypothesis; and a token
--| alphabet, so `formatWithin` can refuse a source before parsing it. The
--| file loop is `crates/fmt/src/printer/mod.rs`'s `print_file_seeing`.

namespace Fmt
import Std (Bool, Doc, List, Nat, Option, Result, Text)
import Std.Doc (..)
import Syntax (Comments, Decl, DefBody, DefKind, Expr, Header, InfixKind, Note, SourceFile, Tok, Word)

-- The slice.

--| Whether the expression is one of slice 1's: a name or numeral, `( )`, a
--| tuple, a list without spreads, an application, a binary operator, `-`
--| or `!`, or `→`, all the way down.
def Expr.within1: Expr → Bool
  | Atom kind _ => kind.wordWithin1
  | Paren _ inner _ => inner.within1
  | Tuple _ items _ _ => allWithin1 items
  | ListOf _ items _ _ => allWithin1 items
  | App head arguments => head.within1 && allWithin1 arguments
  | Infix InfixBinary left _ right => left.within1 && right.within1
  | Infix InfixArrow left _ right => left.within1 && right.within1
  | Prefix _ operand => operand.within1
  | _ => False

def allWithin1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.within1 && allWithin1 rest

--| The token kinds a slice 1 `Atom` may have: names and numerals.
def Tok.wordWithin1: Tok → Bool
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | _ => False

--| `def name: T`: no attributes, `export`, `opaque`, parameters,
--| `decreasing` or `unfolding`.
def Header.within1 (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      forallKeyword = None,
      params = [],
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => result.within1
  | _ => False

def Decl.within1: Decl → Bool
  | Definition [] header (Assigned _ value) => header.within1 && value.within1
  | _ => False

def SourceFile.within1 (file: SourceFile): Bool := file.decls.all Decl.within1

--| Slice 1's tokens: `def`, names, numerals, `:`, `:=`, the brackets, `,`,
--| the binary operators, `-`, `!` and `→`.
def Tok.within1: Tok → Bool
  | KwDef => True
  | Lower => True
  | Upper => True
  | Num => True
  | Float => True
  | Colon => True
  | ColonEq => True
  | LParen => True
  | RParen => True
  | LBracket => True
  | RBracket => True
  | Comma => True
  | OrOr => True
  | AndAnd => True
  | Equals => True
  | EqEq => True
  | NotEq => True
  | Lt => True
  | Le => True
  | Gt => True
  | Ge => True
  | PlusPlus => True
  | Plus => True
  | Minus => True
  | Star => True
  | Slash => True
  | Percent => True
  | Bang => True
  | Arrow => True
  | _ => False

-- Printing.

--| The width lines are fitted to (D1014).
def width: Nat := 120

--| A definition's document (slices 1 and 2), or `None` for another
--| declaration.
def Decl.doc1: Decl → Option Doc
  | Definition [] header (Assigned colonEq value) => Some (defDoc header colonEq value)
  | _ => None

--| A declaration printed in 120 columns, if it is within slice 1.
def Decl.printed1 (decl: Decl): Option Text := if decl.within1 then decl.doc1.map (doc => Doc.print doc width) else None

--| The comments a declaration's first token holds, which the file prints.
def Decl.firstComments: Decl → Comments
  | Definition _ header _ => header.keyword
  | _ => { above = [], after = None, blankBefore = False }

--| The file's text so far, newest piece first, and whether it is empty.
type Output = { pieces: List Text, empty: Bool }

--| One item of the file: a line after the last, with a blank line
--| between if the author had one.
def Output.item (output: Output) (blank: Bool) (text: Text): Output :=
  let gap :=
    if output.empty then []
    else if blank then ["\n\n"]
    else ["\n"]
  { pieces = [text] ++ gap ++ output.pieces, empty = False }

def Output.notes (output: Output): List Note → Output
  | [] => output
  | [note, ..rest] => (output.item note.blankBefore note.text).notes rest

--| The file loop (`print_file_seeing`): each declaration's own-line
--| comments, then the declaration as `printed` gives it, then the comments
--| at the end. Each slice passes its own `printed`.
def SourceFile.printedBy (file: SourceFile) (printed: Decl → Option Text): Text :=
  let body := printDecls printed { pieces = [], empty = True } file.decls
  let done := body.notes file.end.above
  if done.empty then "" else Text.concat ["\n", ..done.pieces].reverse

def printDecls (printed: Decl → Option Text) (output: Output): List Decl → Output
  | [] => output
  | [decl, ..rest] =>
    let first := decl.firstComments
    let noted := output.notes first.above
    printDecls printed (noted.item first.blankBefore ((printed decl).getOrElse "")) rest

def SourceFile.printed1 (file: SourceFile): Text := file.printedBy Decl.printed1

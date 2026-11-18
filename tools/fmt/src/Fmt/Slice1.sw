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
import Std (Bool, Char, Doc, List, Nat, Option, Result, Text)
import Std.Doc (..)
import Syntax (
  Comments,
  Decl,
  DefBody,
  DefKind,
  Expr,
  Header,
  InfixKind,
  Note,
  SourceFile,
  Tok,
  Word,
  isWordChar,
  isWordStart,
  wordKind
)

-- The slice.

--| Whether the expression is one of slice 1's: a name or numeral, `( )`, a
--| tuple, a list without spreads, an application, a binary operator or `→` whose text is one slice 1's alphabet spells, `-`, `!` or `¬`, all the way
--| down.
def Expr.within1: Expr → Bool
  | Atom kind word => kind.wordWithin1 && textSpells1 kind word.text
  | Paren _ inner _ => inner.within1
  | Tuple _ items _ _ => allWithin1 items
  | ListOf _ items _ _ => allWithin1 items
  | App head arguments => head.within1 && allWithin1 arguments
  | Infix InfixBinary left operator right => left.within1 && right.within1 && operatorText1 operator.text
  | Infix InfixArrow left operator right => left.within1 && right.within1 && operatorText1 operator.text
  | Prefix operator operand => operand.within1 && prefixText1 operator.text
  | _ => False

--| The infix operators of slice 1: each text some token of its alphabet is spelled with (`Syntax.Proofs.Spells`),
--| none a comma or closer. `|>` is out: it is no token of the alphabet. In four runs, so the proof that they spell
--| (`operatorSpellsOf`) stays shallow.
def operatorText1 (text: Text): Bool :=
  operatorTextA1 text || operatorTextB1 text || operatorTextC1 text || operatorTextD1 text

def operatorTextA1 (text: Text): Bool :=
  if text == "->" then True
  else if text == "→" then True
  else if text == "||" then True
  else if text == "∨" then True
  else if text == "&&" then True
  else if text == "∧" then True
  else False

def operatorTextB1 (text: Text): Bool :=
  if text == "+" then True
  else if text == "++" then True
  else if text == "-" then True
  else if text == "*" then True
  else if text == "/" then True
  else if text == "%" then True
  else False

def operatorTextC1 (text: Text): Bool :=
  if text == "!=" then True
  else if text == "≠" then True
  else if text == "<" then True
  else if text == "<=" then True
  else if text == "≤" then True
  else False

def operatorTextD1 (text: Text): Bool :=
  if text == ">" then True
  else if text == ">=" then True
  else if text == "≥" then True
  else if text == "==" then True
  else if text == "=" then True
  else False

--| The prefix operators of slice 1: `-`, `!` and `¬`.
def prefixText1 (text: Text): Bool := text == "-" || text == "!" || text == "¬"

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

--| A name or numeral's text is spelled as plainly as the lexer proofs need: a name of word characters (no `.`: a
--| qualified name `List.map` is one `Lower` token the proofs' `Spells` leaves out; not `auto`, which the parser reads
--| as an implicit binder in `[auto Ord]`, so a list that starts with it is no list), a numeral of digits, or digits, a
--| `.` and digits (no exponent: `1e3` is one `Float`). `Syntax.Proofs.Spells` says the same as a proposition
--| (`spellsOfText1`, `textOfSpells1`).
def textSpells1 (kind: Tok) (text: Text): Bool := match kind with
  | Lower => nameText1 Lower text.toList && text != "auto"
  | Upper => nameText1 Upper text.toList
  | Num => numberText1 text.toList
  | Float => floatText1 text.toList
  | _ => False

def nameText1 (kind: Tok) (chars: List Char): Bool := match chars with
  | [first, ..others] => isWordStart first && others.all isWordChar && wordKind False (Text.fromList chars) == kind
  | [] => False

def numberText1 (chars: List Char): Bool := match chars with
  | [first, ..others] => first.isAsciiDigit && others.all Char.isAsciiDigit
  | [] => False

def floatText1 (chars: List Char): Bool := match chars with
  | [first, ..rest] => first.isAsciiDigit && fractionText1 rest
  | [] => False

--| The rest of a float's text: digits, then `.` and a digit and more digits.
def fractionText1 (chars: List Char): Bool := match chars with
  | [] => False
  | [char, ..rest] =>
    if char == '.' then
      match rest with
        | [second, ..more] => second.isAsciiDigit && more.all Char.isAsciiDigit
        | [] => False
    else char.isAsciiDigit && fractionText1 rest

--| A header's name: one token of `Lower` kind, spelled plainly.
def Word.nameWithin1 (word: Word): Bool := word.lexesAs Lower && textSpells1 Lower word.text

--| `def name: T`, with a lower-case name: no attributes, `export`, `opaque`, parameters,
--| `decreasing` or `unfolding`.
def Header.within1 (header: Header): Bool := match header with
  | {
      exportKeyword = None,
      opaqueKeyword = None,
      kind = DefPlain,
      name,
      forallKeyword = None,
      params = [],
      result,
      decreasingClause = None,
      unfoldingClause = None,
      ..
    } => name.nameWithin1 && result.within1
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
  | Namespace keyword _ => keyword
  | Import keyword _ _ _ _ => keyword
  | Test keyword _ _ _ => keyword
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

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
--| down. The name `byWalking` is out (D3706): where an expression starts, `byWalking [` is a walk, slice 6a's.
def Expr.within1: Expr → Bool
  | Atom kind word => kind.wordWithin1 && word.text != "byWalking" && textSpells1 kind word.text
  | Paren _ inner _ => inner.within1
  | Tuple _ items _ _ | ListOf _ items _ _ => allWithin1 items
  | App head arguments => head.within1 && allWithin1 arguments
  | Infix InfixBinary left operator right => left.within1 && right.within1 && binaryText1 operator.text
  | Infix InfixArrow left operator right => left.within1 && right.within1 && arrowText1 operator.text
  | Prefix operator operand => operand.within1 && prefixText1 operator.text
  | _ => False

--| The infix operators of slice 1: each text some token of its alphabet is spelled with (`Syntax.LexProofs.Spells`),
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

--| An arrow's text, `->` or `→`: the operator of an `InfixArrow`, and of no `InfixBinary`, so the kind of infix the
--| tree says is the one the parser reads its token as.
def arrowText1 (text: Text): Bool := text == "->" || text == "→"

--| A binary operator's text: one of slice 1's that is not an arrow.
def binaryText1 (text: Text): Bool := operatorText1 text && !arrowText1 text

--| The prefix operators of slice 1: `-`, `!` and `¬`.
def prefixText1 (text: Text): Bool := text == "-" || text == "!" || text == "¬"

def allWithin1: List Expr → Bool
  | [] => True
  | [expr, ..rest] => expr.within1 && allWithin1 rest

--| The token kinds a slice 1 `Atom` may have: names and numerals.
def Tok.wordWithin1: Tok → Bool
  | Lower | Upper | Num | Float => True
  | _ => False

--| A name or numeral's text is spelled as the lexer proofs need: a name (word characters, or components joined by
--| `.` after an upper-case one, as `List.map`; `auto` too, a name to the lexer), a numeral of digits, or digits with a fraction, an exponent or both
--| (`1.5`, `1e3`, `1.5e-13`). `Syntax.LexProofs.Spells` says the same as a proposition (`spellsOfText1`).
def textSpells1 (kind: Tok) (text: Text): Bool := match kind with
  | Lower => nameText1 Lower text.toList
  | Upper => nameText1 Upper text.toList
  | Num => numberText1 text.toList
  | Float => floatText1 text.toList
  | _ => False

def nameText1 (kind: Tok) (chars: List Char): Bool := match chars with
  | [first, ..others] => isWordStart first && nameRest1 kind (Text.fromList chars) first others
  | [] => False

--| What follows a name's first character: word characters whose kind `wordKind` gives, or a qualified name's
--| components, whose last decides the kind.
def nameRest1 (kind: Tok) (text: Text) (first: Char) (others: List Char): Bool :=
  if others.all isWordChar then wordKind False text == kind
  else qualScan1 first.isAsciiUppercase first.isAsciiUppercase others == Some (kind == Upper)

--| The rest of a qualified name's text, as the lexer's `qualified` reads it: a `.` and a letter go on after a
--| component that starts upper case, and the result is whether the last component does.
def qualScan1 (upper last: Bool): List Char → Option Bool
  | [] => Some last
  | [char, ..more] =>
    if isWordChar char then qualScan1 upper last more
    else if char == '.' then
      match more with
        | [next, ..rest] =>
          if upper && next.isAsciiLetter then qualScan1 next.isAsciiUppercase next.isAsciiUppercase rest else None
        | [] => None
    else None

def numberText1 (chars: List Char): Bool := match chars with
  | [first, ..others] => first.isAsciiDigit && others.all Char.isAsciiDigit
  | [] => False

def floatText1 (chars: List Char): Bool := match chars with
  | [first, ..rest] => first.isAsciiDigit && floatRest1 rest
  | [] => False

--| What follows a float's first digit: digits, then a `.`, a digit and digits, then perhaps an exponent; or digits and
--| an exponent.
def floatRest1: List Char → Bool
  | [] => False
  | [char, ..rest] =>
    if char.isAsciiDigit then floatRest1 rest
    else if char == '.' then
      match rest with
        | [second, ..more] => second.isAsciiDigit && fractionRest1 more
        | [] => False
    else exponentText1 [char, ..rest]

--| The rest of a fraction: digits, then perhaps an exponent.
def fractionRest1: List Char → Bool
  | [] => True
  | [char, ..rest] => if char.isAsciiDigit then fractionRest1 rest else exponentText1 [char, ..rest]

--| An exponent: `e` or `E`, perhaps a sign, and digits.
def exponentText1: List Char → Bool
  | [marker, ..more] => (marker == 'e' || marker == 'E') && exponentDigits1 more
  | [] => False

def exponentDigits1: List Char → Bool
  | [char, ..rest] => if char == '+' || char == '-' then digitsText1 rest else digitsText1 [char, ..rest]
  | [] => False

def digitsText1: List Char → Bool
  | [first, ..others] => first.isAsciiDigit && others.all Char.isAsciiDigit
  | [] => False

--| A header's name: one token of `Lower` or `Upper` kind, spelled as slice 1 has names.
def Word.nameWithin1 (word: Word): Bool :=
  (word.lexesAs Lower && textSpells1 Lower word.text) || (word.lexesAs Upper && textSpells1 Upper word.text)

--| `def name: T`, with a name of either case: no attributes, `export`, `opaque`, parameters,
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
  | KwDef |
      Lower |
      Upper |
      Num |
      Float |
      Colon |
      ColonEq |
      LParen |
      RParen |
      LBracket |
      RBracket |
      Comma |
      OrOr |
      AndAnd |
      Equals |
      EqEq |
      NotEq |
      Lt |
      Le |
      Gt |
      Ge |
      PlusPlus |
      Plus |
      Minus |
      Star |
      Slash |
      Percent |
      Bang |
      Arrow => True
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
  | Namespace keyword _ | Import keyword _ _ _ _ | Test keyword _ _ _ => keyword
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

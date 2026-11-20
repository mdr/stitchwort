--| Stitchwort's tokens, as `crates/syntax`'s lexer gives them to the parser,
--| with the comments and blank lines around each.
--|
--| A token's kind says what it is and nothing more: the text of a name,
--| number or string is the token's slice of the source, which is all the
--| formatter needs. Layout lives on the token (its column, and whether it
--| starts its line), and comments and blank lines on its `Trivia`, so the
--| parser can tell a block's next line from a continuation, and every
--| comment has a token to belong to.

namespace Syntax
import Std (Bool, List, Nat, Option, Text)

--| What a token is: one constructor for each of the Rust lexer's `Tok`
--| variants, with the same names, so the dump can print them as Rust does
--| (`Tok.name`). Literal values aren't kept, since the source slice is.
type Tok =
  | Lower
  | Upper
  | Num
  | Float
  | Str
  --| The opening quote and the text before the first `${` of an
  --| interpolated string: `"a` in `"a${x}b"`.
  | StrStart
  --| The text between a `}` and the next `${`, when there is some.
  | StrMid
  --| The text after the last `}`, with the closing quote: `b"`.
  | StrEnd
  | InterpOpen
  | InterpClose
  | CharLit
  | KwType
  | KwTheorem
  | KwDef
  | KwExport
  | KwTest
  | KwInterface
  | KwInstance
  | TypeU
  | PropU
  | LParen
  | RParen
  | LBracket
  | RBracket
  | Comma
  | Semi
  | Colon
  | ColonEq
  | Equals
  | Arrow
  | Pipe
  | OrOr
  | PipeGt
  | AndAnd
  | Plus
  | PlusPlus
  | Minus
  | Star
  | Slash
  | Percent
  | NotEq
  | EqEq
  | Lt
  | Le
  | Gt
  | Ge
  | Bang
  | KwIn
  | NotIn
  | IffArrow
  | KwExists
  | KwForall
  | KwIf
  | KwThen
  | KwElse
  | KwAbility
  | KwWhere
  | KwHandle
  | KwWith
  | KwMatch
  | KwReturn
  | KwLet
  | KwImport
  | KwInclude
  | KwNamespace
  | KwCalc
  | KwByWalking
  | KwRewrite
  | KwArithmetic
  | KwAlgebra
  | KwCases
  | KwDecreasing
  | KwOpaque
  | KwUnfolding
  | LBrace
  | RBrace
  | FatArrow
  | Underscore
  | Question
  | Dot
  | DotDot
  | DotDotLt
  | DotDotEq
  | At

--| The Rust variant's name, as `dev tokens` prints it. Where a Stitchwort
--| name would clash with std's (`Char`, `Prop`, `Iff`) the constructor is
--| named differently and this gives the Rust name.
def Tok.name: Tok → Text
  | Lower => "Lower"
  | Upper => "Upper"
  | Num => "Num"
  | Float => "Float"
  | Str => "Str"
  | StrStart => "StrStart"
  | StrMid => "StrMid"
  | StrEnd => "StrEnd"
  | InterpOpen => "InterpOpen"
  | InterpClose => "InterpClose"
  | CharLit => "Char"
  | KwType => "KwType"
  | KwTheorem => "KwTheorem"
  | KwDef => "KwDef"
  | KwExport => "KwExport"
  | KwTest => "KwTest"
  | KwInterface => "KwInterface"
  | KwInstance => "KwInstance"
  | TypeU => "TypeU"
  | PropU => "Prop"
  | LParen => "LParen"
  | RParen => "RParen"
  | LBracket => "LBracket"
  | RBracket => "RBracket"
  | Comma => "Comma"
  | Semi => "Semi"
  | Colon => "Colon"
  | ColonEq => "ColonEq"
  | Equals => "Equals"
  | Arrow => "Arrow"
  | Pipe => "Pipe"
  | OrOr => "OrOr"
  | PipeGt => "PipeGt"
  | AndAnd => "AndAnd"
  | Plus => "Plus"
  | PlusPlus => "PlusPlus"
  | Minus => "Minus"
  | Star => "Star"
  | Slash => "Slash"
  | Percent => "Percent"
  | NotEq => "NotEq"
  | EqEq => "EqEq"
  | Lt => "Lt"
  | Le => "Le"
  | Gt => "Gt"
  | Ge => "Ge"
  | Bang => "Bang"
  | KwIn => "KwIn"
  | NotIn => "NotIn"
  | IffArrow => "Iff"
  | KwExists => "KwExists"
  | KwForall => "KwForall"
  | KwIf => "KwIf"
  | KwThen => "KwThen"
  | KwElse => "KwElse"
  | KwAbility => "KwAbility"
  | KwWhere => "KwWhere"
  | KwHandle => "KwHandle"
  | KwWith => "KwWith"
  | KwMatch => "KwMatch"
  | KwReturn => "KwReturn"
  | KwLet => "KwLet"
  | KwImport => "KwImport"
  | KwInclude => "KwInclude"
  | KwNamespace => "KwNamespace"
  | KwCalc => "KwCalc"
  | KwByWalking => "KwByWalking"
  | KwRewrite => "KwRewrite"
  | KwArithmetic => "KwArithmetic"
  | KwAlgebra => "KwAlgebra"
  | KwCases => "KwCases"
  | KwDecreasing => "KwDecreasing"
  | KwOpaque => "KwOpaque"
  | KwUnfolding => "KwUnfolding"
  | LBrace => "LBrace"
  | RBrace => "RBrace"
  | FatArrow => "FatArrow"
  | Underscore => "Underscore"
  | Question => "Question"
  | Dot => "Dot"
  | DotDot => "DotDot"
  | DotDotLt => "DotDotLt"
  | DotDotEq => "DotDotEq"
  | At => "At"

--| The keyword a word spells, ignoring context (`crates/syntax`'s
--| `keyword_table`).
def Tok.keyword: Text → Option Tok
  | "ability" => Some KwAbility
  | "algebra" => Some KwAlgebra
  | "arithmetic" => Some KwArithmetic
  | "byWalking" => Some KwByWalking
  | "calc" => Some KwCalc
  | "cases" => Some KwCases
  | "decreasing" => Some KwDecreasing
  | "def" => Some KwDef
  | "else" => Some KwElse
  | "exists" => Some KwExists
  | "export" => Some KwExport
  | "forall" => Some KwForall
  | "handle" => Some KwHandle
  | "if" => Some KwIf
  | "import" => Some KwImport
  | "in" => Some KwIn
  | "include" => Some KwInclude
  | "instance" => Some KwInstance
  | "interface" => Some KwInterface
  | "let" => Some KwLet
  | "match" => Some KwMatch
  | "namespace" => Some KwNamespace
  | "opaque" => Some KwOpaque
  | "return" => Some KwReturn
  | "rewrite" => Some KwRewrite
  | "test" => Some KwTest
  | "then" => Some KwThen
  | "theorem" => Some KwTheorem
  | "type" => Some KwType
  | "unfolding" => Some KwUnfolding
  | "where" => Some KwWhere
  | "with" => Some KwWith
  | _ => None

--| The token a Unicode spelling of an operator stands for (D1200).
def Tok.unicodeAlias: Char → Option Tok
  | '∈' => Some KwIn
  | '∉' => Some NotIn
  | '→' => Some Arrow
  | '↔' => Some IffArrow
  | '∧' => Some AndAnd
  | '∨' => Some OrOr
  | '¬' => Some Bang
  | '≤' => Some Le
  | '≥' => Some Ge
  | '≠' => Some NotEq
  | '∃' => Some KwExists
  | '∀' => Some KwForall
  | _ => None

def Tok.isOpener: Tok → Bool
  | LParen | LBracket | LBrace => True
  | _ => False

def Tok.isCloser: Tok → Bool
  | RParen | RBracket | RBrace => True
  | _ => False

--| Whether a token can start an atom (`crates/syntax`'s `opens_atom`).
def Tok.opensAtom: Tok → Bool
  | Lower | Upper | Num | Float | Str | StrStart | CharLit | LParen | LBracket | LBrace | Underscore | Question => True
  | _ => False

--| Whether a token starts a declaration, for rule N's search for an
--| expression `let`.
def Tok.startsDeclaration: Tok → Bool
  | KwDef |
      KwTheorem |
      KwType |
      KwTest |
      KwExport |
      KwInstance |
      KwInterface |
      KwNamespace |
      KwImport |
      KwInclude |
      KwAbility => True
  | _ => False

--| A `--` comment: its text from `--` to the end of the line (without a
--| trailing `\r`), its column in bytes, and for a comment on a line of its
--| own, the blank lines just before it (0 for a trailing comment).
type Comment = { text: Text, column: Nat, blankLines: Nat }

--| What surrounds a token, or the end of the file, besides spaces: the
--| comments on lines of their own before it, the blank lines just before its
--| own line, and a comment after it on its line.
type Trivia = {
  leading: List Comment,
  blankLines: Nat,
  trailing: Option Comment
}

def Trivia.empty: Trivia := { leading = [], blankLines = 0, trailing = None }

--| A token: its kind, its slice of the source, its column in bytes from the
--| start of its line (as the Rust lexer counts it), and whether it is the
--| first token on its line.
type Token = { kind: Tok, text: Text, column: Nat, lineStart: Bool }

--| A lexed file: its leaves, and the trivia after the last token (all of
--| the file's comments, if it has no tokens).
type Lexed = { leaves: List Leaf, end: Trivia }

--| Sprig's tokens, as the lexer gives them to the parser.
--|
--| Layout lives in the tokens, not in tokens of its own: each knows whether
--| it starts a line and at what column, so the parser can tell a block's
--| next statement from a continuation line. Comments and blank lines are
--| kept on the tokens beside them: own-line comments and blank lines on the
--| token after them, a comment after code on the token it follows. The
--| texts of names, numbers, strings and comments are slices of the source.

namespace Toy.Syntax
import Std (List, Option, Parse, Text)

type Keyword = | FnKeyword | LetKeyword | IfKeyword | ThenKeyword | ElseKeyword

def Keyword.spelling: Keyword → Text
  | FnKeyword => "fn"
  | LetKeyword => "let"
  | IfKeyword => "if"
  | ThenKeyword => "then"
  | ElseKeyword => "else"

type Punctuation =
  | OpenParen
  | CloseParen
  | OpenSquare
  | CloseSquare
  | Comma
  | Dot
  --| The `=` of a declaration or `let`; `==` is an operator.
  | Defines

type Kind =
  | Name (text: Text)
  | Number (digits: Text)
  --| With its quotes and escapes, as written.
  | Str (written: Text)
  | Reserved (keyword: Keyword)
  | Sign (punctuation: Punctuation)
  | Op (operator: Operator)
  --| Characters no token is made of, or a run of operator characters that
  --| isn't an operator (`=-`): the parser accepts it nowhere, so the error
  --| names it as written.
  | Stray (text: Text)

--| What can come between two tokens besides spaces and the line breaks
--| they are on.
type Trivia =
  --| A comment on a line of its own.
  | OwnLine (comment: Comment)
  --| One or more empty lines.
  | BlankLine

type Token = {
  kind: Kind,
  --| Whether nothing but spaces comes before it on its line.
  startsLine: Bool,
  --| Characters from the start of its line, counting from 0.
  column: Nat,
  --| The own-line comments and blank lines since the token before.
  above: List Trivia,
  --| A comment after it on its line, with where it is.
  trailing: Option (Parse.Located Comment),
  --| Only on the last token: the own-line comments and blank lines after it
  --| to the end of the file.
  below: List Trivia
}

-- The tables, by text patterns.

--| The keyword a word spells, if any.
def Keyword.fromWord: Text → Option Keyword
  | "fn" => Some FnKeyword
  | "let" => Some LetKeyword
  | "if" => Some IfKeyword
  | "then" => Some ThenKeyword
  | "else" => Some ElseKeyword
  | _ => None

--| What a run of operator characters means, if anything.
def symbols: Text → Option Kind
  | "=" => Some (Sign Defines)
  | "||" => Some (Op Or)
  | "&&" => Some (Op And)
  | "==" => Some (Op Equal)
  | "!=" => Some (Op NotEqual)
  | "<" => Some (Op Less)
  | "<=" => Some (Op LessEqual)
  | "++" => Some (Op Append)
  | "+" => Some (Op Plus)
  | "-" => Some (Op Minus)
  | "*" => Some (Op Times)
  | "/" => Some (Op Divide)
  | "%" => Some (Op Remainder)
  | _ => None

--| The punctuation a character is, if any.
def punctuation: Char → Option Punctuation
  | '(' => Some OpenParen
  | ')' => Some CloseParen
  | '[' => Some OpenSquare
  | ']' => Some CloseSquare
  | ',' => Some Comma
  | '.' => Some Dot
  | _ => None

--| A word is a name unless it spells a keyword.
def wordKind (word: Text): Kind := match Keyword.fromWord word with
  | Some reserved => Reserved reserved
  | None => Name word

def symbolsKind (run: Text): Kind := symbols run |> .getOrElse (Stray run)

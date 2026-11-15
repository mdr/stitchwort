--| The lexer: its lexemes cover the source exactly, the tokens know
--| their layout and comments, and the keyword and operator tables.

namespace Toy.Syntax.Tests
import Toy.Syntax (..)
import Std (Fail, List, Option, Parse, Result, Text)

--| The source's lexemes as the texts they were cut from.
def pieces (source: Text): Result (List Text) Text :=
  Fail.toResult (() => Parse.all source lexemes) |> .map (found => found.map (lexeme => cut source lexeme))

def tokens (source: Text): Result (List Token) Text :=
  Fail.toResult (() => Parse.all source (() => lex source)) |> .map (found => found.map (token => token.value))

def kinds (source: Text): Result (List Kind) Text := tokens source |> .map (found => found.map (token => token.kind))

--| Arrows, a combining accent, the last scalar value, a tab and a stray
--| character, in code, strings and comments.
def awkward: Text := "let s = \"→ é 􏿿\" -- ← é\n\tfn → $ x--y\n\n  \"􏿿\""

test "the lexemes joined are the source" := pieces awkward |> .map Text.concat == Ok awkward

test "every lexeme is at least one character" :=
  pieces awkward |> .map (found => found.all (piece => not piece.isEmpty)) == Ok True

test "lengths are in characters" := kinds "\"→→\" →" == Ok [Str "\"→→\"", Stray "→"]

test "a comment ends an operator run" := kinds "x+-- note" == Ok [Name "x", Op Plus]

test "keywords, names, numbers and punctuation" :=
  kinds "fn f(a, b) = if a.x then [1] else b"
    == Ok [
      Reserved FnKeyword,
      Name "f",
      Sign OpenParen,
      Name "a",
      Sign Comma,
      Name "b",
      Sign CloseParen,
      Sign Defines,
      Reserved IfKeyword,
      Name "a",
      Sign Dot,
      Name "x",
      Reserved ThenKeyword,
      Sign OpenSquare,
      Number "1",
      Sign CloseSquare,
      Reserved ElseKeyword,
      Name "b"
    ]

test "line starts and columns" :=
  tokens "fn f() =\n  let x = 1\n  x +\n      y"
    |> .map (found => found.filter (token => token.startsLine) |> .map (token => token.column))
    == Ok [0, 2, 2, 6]

test "comments and blank lines go on the tokens beside them" :=
  match tokens "let a = 1 -- one\n\n\n-- above\nlet b = 2\n-- last\n" with
    | Ok [_, _, _, one, second, _, _, two] =>
      one.trailing.map (comment => comment.value.text) == Some "-- one"
        && second.above.length == 2
        && two.below.length == 1
    | _ => False

test "the keyword table" :=
  ["fn", "let", "if", "then", "else"].map Keyword.fromWord
    == [Some FnKeyword, Some LetKeyword, Some IfKeyword, Some ThenKeyword, Some ElseKeyword]

test "words that aren't keywords" := ["fns", "Let", "", "iff", "_if"].all (word => Keyword.fromWord word == None)

test "the operator table" :=
  ["||", "&&", "==", "!=", "<", "<=", "++", "+", "-", "*", "/", "%"].map symbols
    == [Or, And, Equal, NotEqual, Less, LessEqual, Append, Plus, Minus, Times, Divide, Remainder].map (operator =>
      Some (Op operator))

test "the operator table spells each operator as the printer does" :=
  [Or, And, Equal, NotEqual, Less, LessEqual, Append, Plus, Minus, Times, Divide, Remainder].all (operator =>
    symbols operator.spelling == Some (Op operator))

test "runs that aren't operators" := ["=-", "===", ">", "!", "&"].all (run => symbols run == None)

test "= defines" := symbols "=" == Some (Sign Defines)

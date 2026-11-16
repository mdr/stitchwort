--| Sprig++'s formatter (toy-plus-plus.md §3): parse, the four passes,
--| print. The grammar and the printing rules are not written here: they
--| are the toy's, changed at stages T2 and T3, and stand as open goals so
--| that the theorems about `format` can be stated against them.

namespace Toy.Plus
import Toy.Fmt (FormatResult)
import Toy.Syntax (Lexed, Token, Trivia, lex)
import Std (List, Nat, Parse, Result, Text)

--| The file's grammar over settled tokens, given the comments after the
--| last token: the toy's `sourceFile`, with `:`, `takes`, types, groups
--| and trailing commas, building each closer through `closed`.
def sourceFile (endTrivia: List Trivia): {Parse (Parse.Located Token)} SourceFile := ?

--| The tree of a Sprig++ source: lexed, each comment put where rule N
--| says (`Lexed.settled`), then parsed.
def parse (source: Text): Result SourceFile Text := match lex source with
  | Err message => Err message
  | Ok lexed =>
    match Parse.whole lexed.settled.tokens (() => sourceFile lexed.settled.endTrivia) with
      | Ok file => Ok file
      | Err failure => Err (Parse.tokensMessage source.toList lexed.settled.tokens failure)

--| The printing rules and the engine, at `width`.
def SourceFile.print (file: SourceFile) (width: Nat): Text := ?

def format (source: Text) (width: Nat): FormatResult := match parse source with
  | Err message => ParseError message
  | Ok tree => Formatted (tree.tidy.print width)

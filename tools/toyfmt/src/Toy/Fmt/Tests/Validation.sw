--| The check `format` and `lex` make before answering, on texts where it
--| passes (the cases the theorems in `Toy.Fmt.Proofs` and
--| `Toy.Syntax.Proofs` are about) and where there is nothing to check.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (Option, Result, Text)

test "format answers Stable for an untidy source, and Stable with the same file for its output" :=
  match format untidy 80 with
    | Stable printed => printed.text == tidy && (format printed.text 80).toOption == Some printed
    | Refused _ => False

test "a source that doesn't parse is Refused, with the parser's message" :=
  format broken 80 |> matches | Refused "line 1, column 8: expected an expression, got the end of the input"

test "a source that doesn't lex is Refused, with the lexer's message" :=
  format "let s = \"open" 80 |> matches | Refused _

test "the lexemes of an awkward source cover it" :=
  let awkward := "let s = \"→ é 􏿿\" -- ← é\n\tfn → $ x--y\n\n  \"􏿿\""
  lex awkward |> .map (lexed => covers awkward lexed.lexemes) == Ok True

test "an empty source lexes to no lexemes, which cover it" :=
  lex "" |> .map (lexed => (lexed.lexemes.length, covers "" lexed.lexemes)) == Ok (0, True)

test "a minus before a minus is spaced, so the two don't print as a comment" :=
  ["let y = - -x\n", "let y = - - -f(x)\n", "let y = -(-x) - -x\n"].all (source =>
    format source 80 |> .toOption |> .map (printed => printed.text) == Some source)

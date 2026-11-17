--| The answers `format` and `lex` give, on texts where they succeed (the
--| cases the theorems in `Toy.Fmt.Proofs` and `Toy.Syntax.Proofs` are
--| about) and where there is something to refuse.

namespace Toy.Fmt.Tests
import Toy.Fmt (..)
import Toy.Syntax (..)
import Std (Option, Result, Text)

test "format answers Formatted for an untidy source, and Formatted with the same text for its output" :=
  match format untidy 80 with
    | Formatted text => text == tidy && (format text 80).toOption == Some text
    | ParseError _ => False

test "a source that doesn't parse is a ParseError, with the parser's message" :=
  format broken 80 |> matches | ParseError "line 1, column 8: expected an expression, got the end of the input"

test "a source that doesn't lex is a ParseError, with the lexer's message" :=
  format "let s = \"open" 80 |> matches | ParseError _

test "the lexemes of an awkward source cover it" :=
  let awkward := "let s = \"→ é 􏿿\" -- ← é\n\tfn → $ x--y\n\n  \"􏿿\""
  lex awkward |> .map (lexed => covers awkward lexed.lexemes) == Ok True

test "an empty source lexes to no lexemes, which cover it" :=
  lex "" |> .map (lexed => (lexed.lexemes.length, covers "" lexed.lexemes)) == Ok (0, True)

test "a minus before a minus is spaced, so the two don't print as a comment" :=
  ["let y = - -x\n", "let y = - - -f(x)\n", "let y = x - -x\n"].all (source =>
    format source 80 |> .toOption == Some source)
    && format "let y = -(-x) - -x\n" 80 |> .toOption == Some "let y = - -x - -x\n"

--| A comment ending an `if` inside brackets belongs to the `if`'s last
--| branch. A `,` or closing bracket is printed before it on its line, and
--| rule N gives the comment back to the branch when the text is read.
test "a comma or closing bracket after an if's trailing comment keeps the comment on the if" :=
  ["let y = f(if a then b else c -- k\n, d)\n", "let y = [a, if b then c else d -- k\n]\n",
    "let y = (if a then b else c -- k\n)\n", "let y = f(if a then b else if c then d else e -- k\n, x)\n"].all
    (source =>
      match format source 80 with
        | Formatted text => (format text 80).toOption == Some text
        | ParseError _ => False)

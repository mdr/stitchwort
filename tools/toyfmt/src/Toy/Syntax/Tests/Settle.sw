--| Rule N on the lexer's tokens (`Lexed.settled`): where each comment
--| ends up, and that none is lost.

namespace Toy.Syntax.Tests
import Toy.Syntax (..)
import Std (List, Option, Parse, Result, Text)

--| Each trailing comment after rule N, with the offset of its token.
def trailingAt (source: Text): List (Nat, Text) := match lex source with
  | Err _ => []
  | Ok found =>
    found.settled.tokens.filterMap (token => token.value.trailing.map (comment => (token.offset, comment.value.text)))

--| The own-line comments above each token after rule N, with the token's
--| offset, for the tokens that have some.
def aboveAt (source: Text): List (Nat, List Text) := match lex source with
  | Err _ => []
  | Ok found => found.settled.tokens.filterMap (token =>
    match token.value.above.flatMap Trivia.comments with
      | [] => None
      | comments => Some (token.offset, comments.map (comment => comment.text)))

def settledComments (source: Text): List Text := match lex source with
  | Err _ => []
  | Ok found => found.settled.comments.map (comment => comment.text)

test "a comment after a closer belongs to the last token before it" := trailingAt "[a, b] -- c" == [(4, "-- c")]

test "a comment moves back through several closers and a comma" := trailingAt "f(g(x)), -- c\n" == [(4, "-- c")]

test "a comment after the comma between two items belongs to the first" := trailingAt "[a, -- c\n b]" == [(1, "-- c")]

--| The Rust formatter's `place_comments` loses `-- c1` here.
test "a comment never moves onto a token that has one" :=
  trailingAt "g(f(x) -- c1\n) -- c2" == [(4, "-- c1"), (5, "-- c2")]
    && settledComments "g(f(x) -- c1\n) -- c2" == ["-- c1", "-- c2"]

test "a comment stays on a closer that has own-line comments above it" :=
  trailingAt "[a\n-- above\n] -- c" == [(12, "-- c")] && aboveAt "[a\n-- above\n] -- c" == [(12, ["-- above"])]

test "a comma's own-line comments go above the token after it" :=
  aboveAt "[a\n-- c\n, b -- d\n]" == [(10, ["-- c"])] && settledComments "[a\n-- c\n, b -- d\n]" == ["-- c", "-- d"]

--| So after rule N a token may have own-line comments above it without
--| starting its line, which no token of the lexer's has.
test "a token given a comma's comments keeps its place on the comma's line" :=
  (lex "[a\n-- c\n, b]"
    |> .map (found =>
      found.settled.tokens.filterMap (token =>
        if token.value.above.isEmpty then None else Some (token.offset, token.value.startsLine))))
    == Ok [(10, False)]

test "a comma's comment that can't move back goes above the token after it" :=
  trailingAt "[a -- c\n, -- d\nb]" == [(1, "-- c")] && aboveAt "[a -- c\n, -- d\nb]" == [(15, ["-- d"])]

test "a last comma's comments go to the end of the file" :=
  (lex "a,\n-- c\n" |> .map (found => found.settled.endTrivia)) == Ok [OwnLine { text = "-- c" }]
    && (lex "a\n-- c\n," |> .map (found => found.settled.endTrivia)) == Ok [OwnLine { text = "-- c" }]

test "rule N a second time changes nothing" :=
  ["[a, b] -- c", "f(g(x)), -- c\n", "g(f(x) -- c1\n) -- c2", "[a\n-- c\n, b -- d\n]", "[a -- c\n, -- d\nb]",
    "a,\n\n-- c\n\n, b"]
    |> .all (source =>
      match lex source with
        | Err _ => False
        | Ok found =>
          found.settled.settled.tokens == found.settled.tokens
            && found.settled.settled.endTrivia == found.settled.endTrivia)

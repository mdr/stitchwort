--| Rule N, where a comment belongs (toy-plus-plus.md §3.1), as a function
--| on the lexer's tokens, to run every time tokens are read: a comment
--| written after commas and closing brackets belongs to the last token
--| before them, and a comma holds no comments.
--|
--| The printer writes a closing bracket or comma before a trailing
--| comment that waits on its line (`Toy.Doc.Closing`), so the lexer finds
--| a printed comment on the last closer of its line; this puts it back.
--|
--| It differs from the Rust formatter's `place_comments`
--| (`crates/fmt/src/tidy.rs`) in one way, on purpose: a comment never
--| moves onto a token that already has a trailing comment, whether or not
--| the closer it leaves starts its line. `place_comments` overwrites the
--| comment there (`tools/toyfmt/plus/SKETCH-PLUS.md`, finding 1).

namespace Toy.Syntax
import Std (Bool, List, Option, Parse)

def Kind.isCloser: Kind → Bool
  | Sign CloseParen => True
  | Sign CloseSquare => True
  | _ => False

def Kind.isComma: Kind → Bool
  | Sign Comma => True
  | _ => False

def hasOwnLine (trivia: List Trivia): Bool := trivia.any (matches | OwnLine _)

def trailingSet (token: Parse.Located Token) (trailing: Option (Parse.Located Comment)): Parse.Located Token :=
  { token | value = { token.value | trailing } }

def aboveSet (token: Parse.Located Token) (above: List Trivia): Parse.Located Token :=
  { token | value = { token.value | above } }

--| Whether a trailing comment on `current` moves on to `previous`, the
--| token before it, or past it: `current` is a comma or a closer with no
--| own-line comments above it (they would be left below the comment), and
--| `previous` has no trailing comment of its own.
def movesPast (current previous: Parse.Located Token): Bool :=
  (current.value.kind.isCloser || current.value.kind.isComma)
    && not (hasOwnLine current.value.above)
    && previous.value.trailing.isNone

--| `current` and the tokens before it (newest first), with `comment`,
--| written after `current`, on the token it belongs to.
def homed (comment: Parse.Located Comment) (current: Parse.Located Token) (earlier: List (Parse.Located Token)):
    List (Parse.Located Token) :=
  match earlier with
    | [previous, ..rest] if movesPast current previous => [trailingSet current None, ..homed comment previous rest]
    | _ => [trailingSet current (Some comment), ..earlier]

--| Rule N's first half, for one more token: `earlier` is newest first.
def homeStep (earlier: List (Parse.Located Token)) (token: Parse.Located Token): List (Parse.Located Token) :=
  match token.value.trailing with
    | Some comment if token.value.kind.isCloser || token.value.kind.isComma => homed comment token earlier
    | _ => [token, ..earlier]

--| `front` then `back`, a blank line at the join counted once.
def joinTrivia (front back: List Trivia): List Trivia := match front.last, back with
  | Some BlankLine, [BlankLine, ..rest] => front ++ rest
  | _, _ => front ++ back

def trailingTrivia: Option (Parse.Located Comment) → List Trivia
  | Some comment => [OwnLine comment.value]
  | None => []

--| Rule N's second half: whatever a comma still holds (its own-line
--| comments, and a trailing comment that couldn't move back) goes above
--| the token after it, or to the end of the file. `carried` is what the
--| commas just before `tokens` held.
def carryForward (carried: List Trivia) (tokens: List (Parse.Located Token)) (endTrivia: List Trivia):
    (List (Parse.Located Token), List Trivia) :=
  match tokens with
    | [] => ([], joinTrivia carried endTrivia)
    | [token, ..rest] =>
      let above := joinTrivia carried token.value.above
      if token.value.kind.isComma then
        let (settled, end) := carryForward (joinTrivia above (trailingTrivia token.value.trailing)) rest endTrivia
        ([trailingSet (aboveSet token []) None, ..settled], end)
      else
        let (settled, end) := carryForward [] rest endTrivia
        ([aboveSet token above, ..settled], end)

--| The lexer's tokens with each comment where rule N puts it.
def Lexed.settled (lexed: Lexed): Lexed :=
  let (tokens, endTrivia) := carryForward [] (lexed.tokens.foldLeft [] homeStep).reverse lexed.endTrivia
  { lexed | tokens, endTrivia }

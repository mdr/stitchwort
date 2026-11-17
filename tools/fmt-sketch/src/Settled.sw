--| Rule N's result without layout (spike K1, SW-3825): what `Settled`
--| says of leaves with their columns and line starts left out, and the
--| two statements `printedSettle` rests on, against stage 1's code.
--|
--| Rule 1's limits read the source's line starts, so two layouts of the
--| same tokens and comments can settle differently: in
--| `g (h (x -- a⏎)⏎) -- b` the second `)` keeps `b`, and with the two
--| closers on one line the first does (the Rust rule agrees). Both
--| results are `homed`, and each settles to itself in every layout that
--| starts a line at each closer or bar holding a comment (`laid`), which
--| is the layout the printer writes. So the tree needs no flag: where
--| the comment is held says which layout to print.

namespace Fmt.Sketch.Settled
import Syntax (..)
import Std (Bool, List, Nat, Option, Text)

--| Whether the leaf is one rule 1 may leave a trailing comment on only
--| under its limits: a closer or a record update's `|`.
def holder (leaf: Leaf) (behind ahead: List Leaf): Bool := leaf.kind != Tok.Comma && skipped leaf behind ahead

--| Whether a trailing comment on `leaf` is one rule 1 would leave there
--| wherever the lines break, provided `leaf` starts its line: it has
--| own-line comments, or the code before it ends with a comment, looking
--| back past closers, commas and bars (`endsWithComment`), and for a bar
--| not on the leaf just before (that one rule 1 moves below the bar).
def atHome (leaf: Leaf) (behind ahead: List Leaf): Bool := match behind with
  | [] => True
  | [previous, .._] =>
    (!leaf.trivia.leading.isEmpty || endsWithComment behind [leaf, ..ahead])
      && !(leaf.kind == Tok.Pipe && previous.trivia.trailing.isSome && !ahead.isEmpty)

--| `homed` over `rest`, with `behind` the leaves before, newest first.
def homedFrom (behind rest: List Leaf): Bool := match rest with
  | [] => True
  | [leaf, ..after] =>
    (leaf.trivia.trailing.isNone || !holder leaf behind after || atHome leaf behind after)
      && homedFrom [leaf, ..behind] after

--| Rule 1's result, with no layout: every closer or bar that holds a
--| trailing comment is `atHome`. (Commas and `->` are `settledCommasBare`
--| and `settledArrowsBare`.)
def homed (leaves: List Leaf): Bool := homedFrom [] leaves

def Leaf.startingLine (leaf: Leaf) (lineStart: Bool): Leaf := { leaf | token = { leaf.token | lineStart } }

--| The leaves as the lexer would read them from a text with the same
--| tokens and comments, a line break before each leaf whose choice is
--| `True` and wherever a comment forces one. A trailing comment ends its
--| line, so the lexer finds it on the last of the closers, commas and bars
--| that follow its token on that line. With `keeping`, every `holder` with
--| a trailing comment starts its line too.
def laidFrom (keeping: Bool) (behind: List Leaf) (choices: List Bool) (rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [leaf, ..after] =>
    let choice := choices.head.getOrElse False
    let later := choices.drop 1
    match behind with
      | [] => laidFrom keeping [leaf.startingLine True] later after
      | [previous, ..earlier] =>
        let quiet := leaf.trivia.leading.isEmpty && leaf.trivia.trailing.isNone
        let kept := keeping && leaf.trivia.trailing.isSome && holder leaf behind after
        match previous.trivia.trailing with
          | Some comment if quiet && !choice && skipped leaf behind after =>
            let carried := { leaf.startingLine False | trivia = { leaf.trivia | trailing = Some comment } }
            laidFrom keeping [carried, previous.withTrailing None, ..earlier] later after
          | trailing =>
            let lineStart := trailing.isSome || !leaf.trivia.leading.isEmpty || choice || kept
            laidFrom keeping [leaf.startingLine lineStart, ..behind] later after

def Lexed.laid (lexed: Lexed) (keeping: Bool) (choices: List Bool): Lexed :=
  { lexed | leaves = laidFrom keeping [] choices lexed.leaves }

def Comment.bare (comment: Comment): Comment := { comment | column = 0 }

def Trivia.bare (trivia: Trivia): Trivia :=
  { trivia | leading = trivia.leading.map Comment.bare, trailing = trivia.trailing.map Comment.bare }

def Leaf.bare (leaf: Leaf): Leaf :=
  { token = { leaf.token | column = 0, lineStart = False }, trivia = leaf.trivia.bare }

--| The leaves with every column and line start forgotten: what the tree
--| keeps of them.
def Lexed.bare (lexed: Lexed): Lexed := { leaves = lexed.leaves.map Leaf.bare, end = lexed.end.bare }

--| Whether a comma, closer or bar: the kinds rule 1 walks past, read
--| without the context that tells a record update's bar from another.
def Tok.passable (kind: Tok): Bool := kind == Tok.Comma || kind == Tok.Pipe || kind.isCloser

--| `grammatical` from the second leaf on.
def grammaticalFrom (leaves: List Leaf): Bool := match leaves with
  | [first, second, ..rest] =>
    let next := second.kind
    !(first.kind == Tok.Arrow && (next == Tok.Arrow || next.passable))
      && !(first.kind == Tok.Pipe && next.passable)
      && grammaticalFrom [second, ..rest]
  | _ => True

--| Three things true of every file that parses, without which rule N's
--| result is not `homed`, nor rule N idempotent:
--|
--| 1. The first token is not a comma, closer or bar (rule 1 would leave a
--|    comment on it, having nowhere further back to go).
--| 2. No `->` is followed by another, or by a comma, closer or bar (rule 3
--|    takes the comment rule 1's limit counted on).
--| 3. No `|` is followed by a comma, closer or bar (a record update's bar
--|    would be left a later closer's comment, and rule 1 applied again
--|    moves it below the bar).
def grammatical (leaves: List Leaf): Bool := match leaves with
  | [] => True
  | [first, .._] => !first.kind.passable && grammaticalFrom leaves

--| Whether a comma that starts its line is followed by a comma, closer or
--| bar: in a file that parses, a trailing comma written at the start of
--| the closer's line. Rule 1 can leave a comment on such a comma, a later
--| closer keeps its own because of it, and rule 2 then moves it on, so
--| the result is neither `homed` nor settled: rule N applied again moves
--| the later comment (SW-3825's finding; the Rust rule does the same).
def parkingComma (leaves: List Leaf): Bool := match leaves with
  | [first, second, ..rest] =>
    (first.kind == Tok.Comma && first.token.lineStart && second.kind.passable) || parkingComma [second, ..rest]
  | _ => False

--| What the statements about rule N ask of the leaves the lexer gives it.
def plain (leaves: List Leaf): Bool := grammatical leaves && !parkingComma leaves

-- A candidate for the parking comma: take the comma out before rule N, as
-- the Rust formatter in effect does (its P2 deletes the comma from the
-- text, and rule N runs again on what is left).

--| Whether a comma is followed by another or by a bar: in no file that
--| parses.
def strayComma (leaves: List Leaf): Bool := match leaves with
  | [first, second, ..rest] =>
    (first.kind == Tok.Comma && (second.kind == Tok.Comma || second.kind == Tok.Pipe)) || strayComma [second, ..rest]
  | _ => False

--| The leaves without each comma a closer follows, as the lexer would
--| read the text with those commas deleted: the comma's own-line comments
--| stay above the closer, its trailing comment ends the line before (or,
--| if the comma started its line, stands above the closer too), and the
--| closer starts the line if the comma did.
def withoutLastCommas (behind rest: List Leaf): List Leaf := match rest with
  | [] => behind.reverse
  | [comma, closer, ..after] if comma.kind == Tok.Comma && closer.kind.isCloser =>
    let starts := comma.token.lineStart
    let above := match comma.trivia.trailing with
      | Some comment if starts => comma.trivia.leading ++ [comment.unspaced]
      | _ => comma.trivia.leading
    let closer := (closer.startingLine (starts || closer.token.lineStart)).withLeading (above ++ closer.trivia.leading)
    match comma.trivia.trailing, behind with
      | Some comment, [previous, ..earlier] if !starts =>
        withoutLastCommas [closer, previous.withTrailing (Some comment), ..earlier] after
      | _, _ => withoutLastCommas [closer, ..behind] after
  | [leaf, ..after] => withoutLastCommas [leaf, ..behind] after

--| Rule N after the last commas are taken out.
def Lexed.settledBare (lexed: Lexed): Lexed := { lexed | leaves = withoutLastCommas [] lexed.leaves }.settled

-- Small alphabets, where a search finds closers, commas and comments next
-- to each other often.
--| One leaf of a sample: a kind by number, whether it has an own-line
--| comment and a trailing one, and whether a line breaks before it.
type Cell = { kind: Nat, leading: Bool, trailing: Bool, breaks: Bool }

def Cell.tok (cell: Cell): Tok := match cell.kind % 20 with
  | 16 => Tok.Comma
  | 17 => Tok.RBracket
  | 18 => Tok.Comma
  | 19 => Tok.Lower
  | 0 => Tok.Lower
  | 1 => Tok.Comma
  | 2 => Tok.LParen
  | 3 => Tok.RBracket
  | 4 => Tok.Arrow
  | 5 => Tok.LBrace
  | 6 => Tok.Pipe
  | 7 => Tok.RBrace
  | 8 => Tok.Equals
  | 9 => Tok.ColonEq
  | 10 => Tok.KwLet
  | 11 => Tok.Semi
  | 12 => Tok.Lower
  | _ => Tok.RParen

def spelling (kind: Tok): Text := match kind with
  | Tok.Lower => "x"
  | Tok.Comma => ","
  | Tok.LParen => "("
  | Tok.RBracket => "]"
  | Tok.Arrow => "->"
  | Tok.LBrace => "{"
  | Tok.Pipe => "|"
  | Tok.RBrace => "}"
  | Tok.Equals => "="
  | Tok.ColonEq => ":="
  | Tok.KwLet => "let"
  | Tok.Semi => ";"
  | _ => ")"

--| The cells as leaves, each comment's text naming its cell, so a comment
--| on another token shows. Two things every file that parses has are
--| forced, since rule N is only idempotent with them: the first token is
--| not a comma, closer or bar, and a name follows each `->`.
def sampleFrom (index: Nat) (previous: Option Tok) (cells: List Cell): List Leaf := match cells with
  | [] => []
  | [cell, ..rest] =>
    let comment := (text: Text) => ({ text, column = 0, blankLines = 0 }: Comment)
    let kind := if previous == None || previous == Some Tok.Arrow then Tok.Lower else cell.tok
    let leaf: Leaf := {
      token = { kind, text = spelling kind, column = 0, lineStart = False },
      trivia = {
        leading = if cell.leading then [comment "-- above ${index}"] else [],
        blankLines = 0,
        trailing = if cell.trailing then Some (comment "-- after ${index}") else None
      }
    }
    [leaf, ..sampleFrom (index + 1) (Some kind) rest]

def sample (cells: List Cell): Lexed :=
  ({ leaves = sampleFrom 0 None cells, end = Trivia.empty }: Lexed).laid False (cells.map (cell => cell.breaks))

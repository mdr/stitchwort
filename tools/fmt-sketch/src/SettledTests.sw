--| Spike K1's cases on real text (SW-3825): the layout that rule N's
--| result does depend on, and the comma its statements leave out.

namespace Fmt.Sketch.SettledTests
import Fmt.Sketch.Settled (..)
import Std (Bool, List, Option, Result, Text)
import Syntax (Leaf, Lexed, lex)

def lexed (source: Text): Lexed := match lex source with
  | Ok lexed => lexed
  | Err _ => { leaves = [], end = Syntax.Trivia.empty }

--| The text of each token with a trailing comment, with the comment.
def trailing (lexed: Lexed): List (Text, Text) :=
  lexed.leaves.filterMap (leaf => leaf.trivia.trailing.map (comment => (leaf.token.text, comment.text)))

--| The closers of `g (h (x -- a⏎)⏎) -- b`, on two lines and on one.
def twoLines: Lexed := (lexed "g (h (x -- a\n)\n) -- b\n").settled

def oneLine: Lexed := (lexed "g (h (x -- a\n)) -- b\n").settled

test "which closer keeps a comment depends on the line breaks" :=
  twoLines.leaves.map (leaf => leaf.trivia.trailing.isSome) == [False, False, False, False, True, False, True]
    && oneLine.leaves.map (leaf => leaf.trivia.trailing.isSome) == [False, False, False, False, True, True, False]

test "both results are homed, and each settles to itself with its holder starting a line" :=
  homed twoLines.leaves
    && homed oneLine.leaves
    && (twoLines.laid True []).settled.bare == twoLines.bare
    && (oneLine.laid True []).settled.bare == oneLine.bare

--| A trailing comma at the start of the closer's line, comments above it.
def parking: Lexed := lexed "g ([\n  1\n  -- above\n  , ] -- b\n) -- c\n"

test "a comma that starts the closer's line: rule N's result is not homed, nor settled" :=
  parkingComma parking.leaves
    && trailing parking.settled == [(")", "-- c")]
    && !homed parking.settled.leaves
    && trailing parking.settled.settled == [("1", "-- c")]
    && trailing (parking.settled.laid True []).settled == [("]", "-- c")]

test "with the comma taken out first, it is both, and the Rust formatter's answer" :=
  trailing parking.settledBare == [("]", "-- b"), (")", "-- c")]
    && homed parking.settledBare.leaves
    && parking.settledBare.settled == parking.settledBare

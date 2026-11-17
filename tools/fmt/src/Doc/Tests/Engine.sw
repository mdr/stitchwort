--| The Rust engine's own tests (`crates/fmt/src/printer/engine.rs`), ported:
--| six of its eight, leaving out the two on `Verbatim` and `LineStart`,
--| which this engine doesn't have.

namespace Fmt.Doc.Tests
import Fmt.Doc (..)
import Std (List)

def t (text: Text): Doc := Doc.text text

--| `[a, b, …]` as a comma bracket.
def bracketList (items: List Text): Doc :=
  let inner := items.withIndex.concatMap (((index, item)) =>
    let before := if index == 0 then SoftLine else Line
    let comma := if index + 1 < items.length then [t ","] else []
    [before, t item, ..comma])
  Doc.group (Doc.concat [t "[", Nest 2 (Doc.concat inner), SoftLine, t "]"])

test "a group prints flat when it fits" := print (bracketList ["a", "b"]) 120 == "[a, b]"

test "a group that doesn't fit breaks every line" := print (bracketList ["a", "b"]) 5 == "[\n  a,\n  b\n]"

-- `[a, b]` is 6 wide and fits in 7, but not with ` :=` after it.
def followed: Doc := Doc.concat [bracketList ["a", "b"], t " :="]

test "what follows a group on its line counts" :=
  print followed 9 == "[a, b] :=" && print followed 8 == "[\n  a,\n  b\n] :="

def wide: Doc := Doc.group (Doc.concat [t "∀∀∀", Line, t "→→"])

test "width is counted in characters" := print wide 6 == "∀∀∀ →→" && print wide 5 == "∀∀∀\n→→"

test "a fill breaks only before an item that doesn't fit" :=
  print (Fill [t "aaa", t "bbb", t "ccc", t "d"]) 8 == "aaa bbb\nccc d"

def hugged: Doc :=
  let hug := Doc.concat [t "f a (x =>", Nest 2 (Doc.concat [HardLine, t "body)"])]
  let broken := Doc.concat [t "f", Nest 2 (Doc.concat [HardLine, t "a", HardLine, t "(x => body)"])]
  Choice [Flatten (t "f a (x => body)"), hug, broken]

test "a choice takes the first option whose first line fits" :=
  print hugged 20 == "f a (x => body)"
    && print hugged 10 == "f a (x =>\n  body)"
    && print hugged 5 == "f\n  a\n  (x => body)"

test "a trailing comment waits for the end of its line" :=
  print (Doc.concat [t "x", LineSuffix "-- c", HardLine, t "y"]) 120 == "x -- c\ny"

--| A chunk after a trailing comment starts a line, a bracket's text too:
--| only a `Closing` joins the comment's line.
test "code after a trailing comment starts a continuation line, without the space before it" :=
  print (Doc.concat [t "x", LineSuffix "-- c", t ")", HardLine, t "y"]) 120 == "x -- c\n  )\ny"
    && print (Nest 6 (Doc.concat [t "x", LineSuffix "-- c", t " ", t "y"])) 120 == "x -- c\n      y"

--| What follows the comment goes on a line indented as the comment's.
test "an own-line comment no layout broke for starts a continuation line" :=
  let comment := Doc.concat [t "f", LineStart, t "-- c", CommentEnd, t "x"]
  print comment 120 == "f\n  -- c\n  x"
    && print (Doc.concat [comment, HardLine, t "y"]) 120 == "f\n  -- c\n  x\ny"
    && print (Doc.concat [t "f", HardLine, LineStart, t "-- c", CommentEnd, t "x"]) 120 == "f\n-- c\nx"
    && print (Doc.concat [t "f +", t " ", LineStart, t "-- c", CommentEnd, t "x"]) 120 == "f +\n  -- c\n  x"
    && print (Nest 4 (Doc.concat [t "f", HardLine, LineStart, t "-- c", CommentEnd, t "x"])) 120 == "f\n    -- c\n    x"

test "comments before a closer go at the indentation in force" :=
  let comments := Nest 2 (Doc.concat [LineStartHere, t "-- c"])
  print (Doc.concat [t "[x", comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"
    && print (Doc.concat [t "[x", HardLine, comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"

test "a group that would put code after a trailing comment breaks" :=
  print (Doc.group (Doc.concat [t "f a", LineSuffix "-- c", Line, t "b"])) 120 == "f a -- c\nb"

test "a group after a waiting trailing comment breaks rather than put code after it" :=
  print (Doc.concat [t "f a", LineSuffix "-- c", Doc.group (Doc.concat [Line, t "b"])]) 120 == "f a -- c\nb"

test "a closer joins the line of a waiting trailing comment, before it" :=
  print (Doc.concat [t "[a", LineSuffix "-- c", Closing "]", HardLine, t "y"]) 120 == "[a] -- c\ny"
    && print (Doc.concat [t "f(g(a", LineSuffix "-- c", Closing ")", Closing ")"]) 120 == "f(g(a)) -- c"
    && print (Doc.concat [t "a", LineSuffix "-- c", Closing ",", Line, t "b"]) 120 == "a, -- c\nb"

test "a closer after the comment's line has ended is on the next line" :=
  print (Doc.concat [t "a", LineSuffix "-- c", HardLine, Closing ")"]) 120 == "a -- c\n)"

--| `[a, b -- c]`: the `]` is measured on the comment's line.
def closedList: Doc := Doc.group (Doc.concat [t "[", Fill [t "a,", Doc.concat [t "b", LineSuffix "-- c"]], Closing "]"])

test "a group stays flat when only closers follow a trailing comment" :=
  print closedList 120 == "[a, b] -- c" && print closedList 6 == "[a, b] -- c" && print closedList 5 == "[a,\nb] -- c"

test "a closer with no comment waiting is a chunk" :=
  print (Doc.concat [t "(", t "a", Closing ")"]) 120 == "(a)" && print (Closing "") 120 == ""

--| A call keeps a `SoftLine` before its `)`, which breaks where a comment
--| waits; a rule that wants `f(a, b) -- c` offers the flat call, with no
--| `SoftLine`, as the first option of a choice.
def closedCall: Doc :=
  let arguments := Doc.concat [t "a,", Line, t "b", LineSuffix "-- c"]
  Choice [
    Flatten (Doc.concat [t "f(", arguments, Closing ")"]),
    Doc.group (Doc.concat [t "f(", Nest 2 (Doc.concat [SoftLine, arguments]), SoftLine, Closing ")"])
  ]

test "a choice puts a call's closer on its comment's line when the call fits" :=
  print closedCall 120 == "f(a, b) -- c" && print closedCall 6 == "f(\n  a,\n  b -- c\n)"

--| `f -- c` then a call: its group is measured from the line the comment
--| break starts, at 2 in, so it stays flat while `  (1)` fits there.
def callAfterComment: Doc :=
  let call := Doc.group (Doc.concat [t "(", Nest 2 (Doc.concat [SoftLine, t "1"]), SoftLine, Closing ")"])
  Doc.concat [t "f", LineSuffix "-- c", Nest 2 call]

test "a group after a waiting trailing comment is measured from the line its code starts" :=
  print callAfterComment 120 == "f -- c\n  (1)"
    && print callAfterComment 5 == "f -- c\n  (1)"
    && print callAfterComment 4 == "f -- c\n  (\n    1\n  )"

--| The new line is at least 2 deeper than the comment's, whatever the
--| construct's indentation, and the spaces before the code are dropped.
test "the measure after a comment break starts 2 in from the comment's line" :=
  let group := Doc.group (Doc.concat [t "a", Line, t "b"])
  let doc := Nest 4 (Doc.concat [HardLine, t "x", LineSuffix "-- c", t " ", group])
  print doc 9 == "\n    x -- c\n      a b" && print doc 8 == "\n    x -- c\n      a\n    b"

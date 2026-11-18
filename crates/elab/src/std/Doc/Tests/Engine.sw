--| The Rust engine's own tests (`crates/fmt/src/printer/engine.rs`), ported,
--| leaving out the ones on text blocks, which this engine doesn't have,
--| and tests of its own for the closer marks, which Rust's lack.

import Doc (..)
import Bool (not)
import Doc.Tests (..)

def Doc.Tests.t (text: Text): Doc := Doc.text text

--| `[a, b, …]` as a comma bracket.
def Doc.Tests.bracketList (items: List Text): Doc :=
  let inner := items.withIndex.concatMap (((index, item)) =>
    let before := if index == 0 then SoftLine else Line
    let comma := if index + 1 < items.length then [t ","] else []
    [before, t item, ..comma])
  Doc.group (Doc.concat [t "[", Nest 2 (Doc.concat inner), SoftLine, t "]"])

test "a group prints flat when it fits" := Doc.print (bracketList ["a", "b"]) 120 == "[a, b]"

test "a group that doesn't fit breaks every line" := Doc.print (bracketList ["a", "b"]) 5 == "[\n  a,\n  b\n]"

-- `[a, b]` is 6 wide and fits in 7, but not with ` :=` after it.
def Doc.Tests.followed: Doc := Doc.concat [bracketList ["a", "b"], t " :="]

test "what follows a group on its line counts" :=
  Doc.print followed 9 == "[a, b] :=" && Doc.print followed 8 == "[\n  a,\n  b\n] :="

def Doc.Tests.wide: Doc := Doc.group (Doc.concat [t "∀∀∀", Line, t "→→"])

test "width is counted in characters" := Doc.print wide 6 == "∀∀∀ →→" && Doc.print wide 5 == "∀∀∀\n→→"

test "a fill breaks only before an item that doesn't fit" :=
  Doc.print (Fill [t "aaa", t "bbb", t "ccc", t "d"]) 8 == "aaa bbb\nccc d"

def Doc.Tests.hugged: Doc :=
  let hug := Doc.concat [t "f a (x =>", Nest 2 (Doc.concat [HardLine, t "body)"])]
  let broken := Doc.concat [t "f", Nest 2 (Doc.concat [HardLine, t "a", HardLine, t "(x => body)"])]
  Choice [Flatten (t "f a (x => body)"), hug, broken]

test "a choice takes the first option whose first line fits" :=
  Doc.print hugged 20 == "f a (x => body)"
    && Doc.print hugged 10 == "f a (x =>\n  body)"
    && Doc.print hugged 5 == "f\n  a\n  (x => body)"

test "a trailing comment waits for the end of its line" :=
  Doc.print (Doc.concat [t "x", LineSuffix "-- c", HardLine, t "y"]) 120 == "x -- c\ny"

--| A chunk after a trailing comment starts a line, a bracket's text too:
--| only a `Closing` joins the comment's line.
test "code after a trailing comment starts a continuation line, without the space before it" :=
  Doc.print (Doc.concat [t "x", LineSuffix "-- c", t ")", HardLine, t "y"]) 120 == "x -- c\n  )\ny"
    && Doc.print (Nest 6 (Doc.concat [t "x", LineSuffix "-- c", t " ", t "y"])) 120 == "x -- c\n      y"

--| What follows the comment goes on a line indented as the comment's.
test "an own-line comment no layout broke for starts a continuation line" :=
  let comment := Doc.concat [t "f", LineStart, t "-- c", HardLine, t "x"]
  Doc.print comment 120 == "f\n  -- c\n  x"
    && Doc.print (Doc.concat [comment, HardLine, t "y"]) 120 == "f\n  -- c\n  x\ny"
    && Doc.print (Doc.concat [t "f", HardLine, LineStart, t "-- c", HardLine, t "x"]) 120 == "f\n-- c\nx"
    && Doc.print (Doc.concat [t "f +", t " ", LineStart, t "-- c", HardLine, t "x"]) 120 == "f +\n  -- c\n  x"
    && Doc.print (Nest 4 (Doc.concat [t "f", HardLine, LineStart, t "-- c", HardLine, t "x"])) 120
      == "f\n    -- c\n    x"

test "the comment floor lasts until the next code" :=
  Doc.print (Doc.concat [t "f", LineStart, t "-- c", HardLine, t "-- d", HardLine, t "x", HardLine, t "y"]) 120
    == "f\n  -- c\n  -- d\n  x\ny"
    && Doc.print (Doc.concat [t "f", LineStart, t "-- c", Nest 4 (Doc.concat [HardLine, t "x"])]) 120
      == "f\n  -- c\n    x"

test "spaces after a trailing comment are held for a closer" :=
  Doc.print (Doc.concat [t "Both (", LineSuffix "-- c", t " ", Closing ")"]) 120 == "Both ( ) -- c"
    && Doc.print (Doc.concat [t "f", LineSuffix "-- c", t " ", HardLine, t "x"]) 120 == "f -- c\nx"

test "a flat line after a trailing comment holds a space, and code after it starts a line" :=
  Doc.print (Flatten (Doc.concat [t "(a +", LineSuffix "-- c", Line, t "b", Closing ")"])) 120 == "(a + -- c\n  b)"
    && Doc.print (Doc.group (Doc.concat [t "g (a,", Line, t "b", LineSuffix "-- c", SoftLine, Closing ")"])) 120
      == "g (a, b) -- c"

test "spaces held before a closer after a comment count in the measure" :=
  let option := Doc.concat [t "aaaa", LineSuffix "-- c", t " ", t " ", Closing "}"]
  Doc.print (Choice [option, t "alt"]) 5 == "alt" && Doc.print (Choice [option, t "alt"]) 7 == "aaaa  } -- c"

test "comments before a closer go at the indentation in force" :=
  let comments := Nest 2 (Doc.concat [LineStartHere, t "-- c"])
  Doc.print (Doc.concat [t "[x", comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"
    && Doc.print (Doc.concat [t "[x", HardLine, comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"

test "a group that would put code after a trailing comment breaks" :=
  Doc.print (Doc.group (Doc.concat [t "f a", LineSuffix "-- c", Line, t "b"])) 120 == "f a -- c\nb"

test "a group after a waiting trailing comment breaks rather than put code after it" :=
  Doc.print (Doc.concat [t "f a", LineSuffix "-- c", Doc.group (Doc.concat [Line, t "b"])]) 120 == "f a -- c\nb"

test "a closer joins the line of a waiting trailing comment, before it" :=
  Doc.print (Doc.concat [t "[a", LineSuffix "-- c", Closing "]", HardLine, t "y"]) 120 == "[a] -- c\ny"
    && Doc.print (Doc.concat [t "f(g(a", LineSuffix "-- c", Closing ")", Closing ")"]) 120 == "f(g(a)) -- c"
    && Doc.print (Doc.concat [t "a", LineSuffix "-- c", Closing ",", Line, t "b"]) 120 == "a, -- c\nb"

test "a closer after the comment's line has ended is on the next line" :=
  Doc.print (Doc.concat [t "a", LineSuffix "-- c", HardLine, Closing ")"]) 120 == "a -- c\n)"

--| `[a, b -- c]`: the `]` is measured on the comment's line.
def Doc.Tests.closedList: Doc :=
  Doc.group (Doc.concat [t "[", Fill [t "a,", Doc.concat [t "b", LineSuffix "-- c"]], Closing "]"])

test "a group stays flat when only closers follow a trailing comment" :=
  Doc.print closedList 120 == "[a, b] -- c"
    && Doc.print closedList 6 == "[a, b] -- c"
    && Doc.print closedList 5 == "[a,\nb] -- c"

test "a closer with no comment waiting is a chunk" :=
  Doc.print (Doc.concat [t "(", t "a", Closing ")"]) 120 == "(a)" && Doc.print (Closing "") 120 == ""

--| A call whose last argument has a trailing comment: flat, its `)` joins
--| the comment's line; broken, it starts a line of its own.
def Doc.Tests.closedCall: Doc :=
  let arguments := Doc.concat [t "a,", Line, t "b", LineSuffix "-- c"]
  Choice [
    Flatten (Doc.concat [t "f(", arguments, Closing ")"]),
    Doc.group (Doc.concat [t "f(", Nest 2 (Doc.concat [SoftLine, arguments]), SoftLine, Closing ")"])
  ]

test "a choice puts a call's closer on its comment's line when the call fits" :=
  Doc.print closedCall 120 == "f(a, b) -- c" && Doc.print closedCall 6 == "f(\n  a,\n  b -- c\n)"

--| `f -- c` then a call: its group is measured from the line the comment
--| break starts, at 2 in, so it stays flat while `  (1)` fits there.
def Doc.Tests.callAfterComment: Doc :=
  let call := Doc.group (Doc.concat [t "(", Nest 2 (Doc.concat [SoftLine, t "1"]), SoftLine, Closing ")"])
  Doc.concat [t "f", LineSuffix "-- c", Nest 2 call]

test "a group after a waiting trailing comment is measured from the line its code starts" :=
  Doc.print callAfterComment 120 == "f -- c\n  (1)"
    && Doc.print callAfterComment 5 == "f -- c\n  (1)"
    && Doc.print callAfterComment 4 == "f -- c\n  (\n    1\n  )"

--| The new line is at least 2 deeper than the comment's, whatever the
--| construct's indentation, and the spaces before the code are dropped.
test "the measure after a comment break starts 2 in from the comment's line" :=
  let group := Doc.group (Doc.concat [t "a", Line, t "b"])
  let doc := Nest 4 (Doc.concat [HardLine, t "x", LineSuffix "-- c", t " ", group])
  Doc.print doc 9 == "\n    x -- c\n      a b" && Doc.print doc 8 == "\n    x -- c\n      a\n    b"

--| What `balanced_fill` measures its items with (`Doc.flatWidth` here).
test "flat width counts characters, with a line as one space" :=
  wide.flatWidth == Some 6
    && (bracketList ["a", "b"]).flatWidth == Some 6
    && (Doc.Nothing |> .flatWidth) == Some 0
    && (t "→").flatWidth == Some 1

test "a document that must break has no flat width" :=
  (Doc.concat [t "a", HardLine, t "b"]).flatWidth == None
    && (BreakParent |> .flatWidth) == None
    && (OneLineBelow (t "a")).flatWidth == None
    && (Doc.concat [t "a", LineStart, t "-- c"]).flatWidth == None

test "a flat width is that of the flat Doc.print, whatever the layout would do" :=
  (Fill [t "aaa", t "bbb", t "ccc"]).flatWidth == Some 11
    && (Choice [Flatten (t "f a"), Doc.concat [t "f", HardLine, t "a"]]).flatWidth == Some 3
    && (Doc.concat [t "x", LineSuffix "-- c"]).flatWidth == Some 6
    && (Doc.concat [t "a", Closing ")"]).flatWidth == Some 2

--| A header whose group records its decision, and a body that goes below
--| it if it broke: `def f (x: Nat) := x`, or the body on a line of its own.
def Doc.Tests.headerAndBody: Doc :=
  let header := Doc.concat [t "def f", Nest 4 (Doc.concat [Line, t "(x: Nat)"])] |> .idGroup 1
  Doc.concat [header, IfBroken 1 (Nest 2 (Doc.concat [HardLine, t ":= x"])) (t " := x")]

test "an IfBroken takes its broken branch after its group broke" :=
  Doc.print headerAndBody 120 == "def f (x: Nat) := x" && Doc.print headerAndBody 16 == "def f\n    (x: Nat)\n  := x"

test "an IfBroken whose group hasn't printed takes its flat branch" := Doc.print (IfBroken 9 (t "b") (t "f")) 120 == "f"

-- The id group is 22 columns at width 20, so it breaks and the option below
-- takes `IfBroken`'s broken branch: 19 columns on a line at 2, more than the
-- 18 there, so the option doesn't fit, where the flat branch would have.
def Doc.Tests.belowAfterBroken: Doc :=
  let wide := "w".repeat 20
  let group := Doc.concat [t wide, Line, t "z"] |> .idGroup 7
  let below := OneLineBelow (IfBroken 7 (t ("b".repeat 19)) (t "short"))
  Doc.concat [group, HardLine, Choice [below, t "alt"]]

test "an IfBroken in a one-line-below option sees an earlier group's mode" :=
  Doc.print belowAfterBroken 20 == "${"w".repeat 20}\nz\nalt"

-- SW-3728: the element's first line keeps the element's indentation even
-- when a part inside it (`f a`, a call's arguments at 4) would break
-- deeper, so the element's next line isn't left of its first.
def Doc.Tests.displacedAfterComment: Doc :=
  let block := Displaced (Doc.concat [Nest 4 (t "f a"), HardLine, t "b"])
  Nest 2 (Doc.concat [t "=>", LineSuffix "-- c", t " ", block])

test "a comment break at a displaced element starts its own line" :=
  Doc.print displacedAfterComment 120 == "=> -- c\n  f a\n  b"

def Doc.Tests.twoLines: Doc := Doc.concat [t "a", HardLine, t "b"]

test "an align indents its line breaks to the column it starts at" :=
  Doc.print (Doc.concat [t "(let ", Align twoLines]) 120 == "(let a\n     b"

test "an align inset at a line start indents its line breaks 2 columns in" :=
  Doc.print (Doc.concat [t "x", HardLine, AlignInset twoLines]) 120 == "x\na\n  b"
    && Doc.print (Doc.concat [t "x ", AlignInset twoLines]) 120 == "x a\n  b"

def Doc.Tests.narrow: Doc := Doc.concat [t "aaaa", Line, t "bbbb"] |> .narrowGroup 10

test "a narrow group is flat only if its line ends within its columns" :=
  Doc.print narrow 120 == "aaaa bbbb" && Doc.print (Doc.concat [t "xx", narrow]) 120 == "xxaaaa\nbbbb"

test "a closer line goes at the indentation in force when no line since its mark is left of it" :=
  let body := Nest 2 (Doc.concat [HardLine, t "x"])
  Doc.print (Nest 2 (Doc.concat [t "f", HardLine, Mark 0, t "(", body, CloserLine 0, t ")"])) 120
    == "f\n  (\n    x\n  )"

test "a closer line goes at its marked line's indentation when a line since is left of it" :=
  let opened := Nest 2 (Doc.concat [HardLine, Mark 0, t "("])
  Doc.print (Doc.concat [t "f", opened, HardLine, t "y", Nest 4 (CloserLine 0), t ")"]) 120 == "f\n  (\ny\n  )"

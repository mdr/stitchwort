/-
The toy's engine tests (`tools/toyfmt/src/Toy/Doc/Tests/Engine.sw`),
all twelve, as `#guard`s: the file fails to check if one is false.
-/
import Toy.Print

namespace Toy.Tests
open Toy Doc

def t (text : String) : Doc := Doc.text (Text.ofString text)
def c (comment : String) : Doc := LineSuffix (Text.ofString comment)
def printed (doc : Doc) (width : Nat) : String := (print doc width).toString

def bracketList (items : List String) : Doc :=
  let inner := items.zipIdx.flatMap (fun (item, index) =>
    let before := if index == 0 then SoftLine else Line
    let comma := if index + 1 < items.length then [t ","] else []
    before :: t item :: comma)
  Doc.group (Doc.concat [t "[", Nest 2 (Doc.concat inner), SoftLine, t "]"])

-- a group prints flat when it fits
#guard printed (bracketList ["a", "b"]) 120 == "[a, b]"

-- a group that doesn't fit breaks every line
#guard printed (bracketList ["a", "b"]) 5 == "[\n  a,\n  b\n]"

def followed : Doc := Doc.concat [bracketList ["a", "b"], t " :="]

-- what follows a group on its line counts
#guard printed followed 9 == "[a, b] :=" && printed followed 8 == "[\n  a,\n  b\n] :="

def wide : Doc := Doc.group (Doc.concat [t "∀∀∀", Line, t "→→"])

-- width is counted in characters
#guard printed wide 6 == "∀∀∀ →→" && printed wide 5 == "∀∀∀\n→→"

-- a fill breaks only before an item that doesn't fit
#guard printed (Fill [t "aaa", t "bbb", t "ccc", t "d"]) 8 == "aaa bbb\nccc d"

def hugged : Doc :=
  let hug := Doc.concat [t "f a (x =>", Nest 2 (Doc.concat [HardLine, t "body)"])]
  let broken := Doc.concat [t "f", Nest 2 (Doc.concat [HardLine, t "a", HardLine, t "(x => body)"])]
  Choice [Flatten (t "f a (x => body)"), hug, broken]

-- a choice takes the first option whose first line fits
#guard printed hugged 20 == "f a (x => body)"
  && printed hugged 10 == "f a (x =>\n  body)"
  && printed hugged 5 == "f\n  a\n  (x => body)"

-- a trailing comment waits for the end of its line
#guard printed (Doc.concat [t "x", c "-- c", HardLine, t "y"]) 120 == "x -- c\ny"

-- code after a trailing comment starts a continuation line, without the space before it
#guard printed (Doc.concat [t "x", c "-- c", t ")", HardLine, t "y"]) 120 == "x -- c\n  )\ny"
  && printed (Nest 6 (Doc.concat [t "x", c "-- c", t " ", t "y"])) 120 == "x -- c\n      y"

def comment : Doc := Doc.concat [t "f", LineStart, t "-- c", CommentEnd, t "x"]

-- an own-line comment no layout broke for starts a continuation line
#guard printed comment 120 == "f\n  -- c\n  x"
  && printed (Doc.concat [comment, HardLine, t "y"]) 120 == "f\n  -- c\n  x\ny"
  && printed (Doc.concat [t "f", HardLine, LineStart, t "-- c", CommentEnd, t "x"]) 120 == "f\n-- c\nx"
  && printed (Doc.concat [t "f +", t " ", LineStart, t "-- c", CommentEnd, t "x"]) 120 == "f +\n  -- c\n  x"
  && printed (Nest 4 (Doc.concat [t "f", HardLine, LineStart, t "-- c", CommentEnd, t "x"])) 120
    == "f\n    -- c\n    x"

def comments : Doc := Nest 2 (Doc.concat [LineStartHere, t "-- c"])

-- comments before a closer go at the indentation in force
#guard printed (Doc.concat [t "[x", comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"
  && printed (Doc.concat [t "[x", HardLine, comments, HardLine, t "]"]) 120 == "[x\n  -- c\n]"

-- a group that would put code after a trailing comment breaks
#guard printed (Doc.group (Doc.concat [t "f a", c "-- c", Line, t "b"])) 120 == "f a -- c\nb"

-- a group after a waiting trailing comment breaks rather than put code after it
#guard printed (Doc.concat [t "f a", c "-- c", Doc.group (Doc.concat [Line, t "b"])]) 120 == "f a -- c\nb"

end Toy.Tests

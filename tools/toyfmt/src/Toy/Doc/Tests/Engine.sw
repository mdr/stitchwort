--| The Rust engine's own tests (`crates/fmt/src/printer/engine.rs`), ported:
--| six of its eight, leaving out the two on `Verbatim` and `LineStart`,
--| which this engine doesn't have.

namespace Toy.Doc.Tests
import Toy.Doc (..)
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
  print (Doc.concat [t "x", LineSuffix "-- c", t ")", HardLine, t "y"]) 120 == "x) -- c\ny"

test "a group that would put code after a trailing comment breaks" :=
  print (Doc.group (Doc.concat [t "f a", LineSuffix "-- c", Line, t "b"])) 120 == "f a -- c\nb"

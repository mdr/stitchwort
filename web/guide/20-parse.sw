-- `Parse` is an ability for reading structured text. A parser is ordinary
-- code: `nat()` reads a number, `char ','` a given character, and a failure
-- says where and what was expected.
import Std (Fail, List, Parse, Result, Text)
import Std.Fail (toResult)
import Std.Parse (char, nat)

type Rect = { width: Nat, height: Nat }

def rect(): {Parse} Rect :=
  let width := nat()
  char 'x'
  let height := nat()
  { width, height }

-- `Parse.eachLine` parses every line with it; `Fail` reports the first
-- line that doesn't fit.
def parseRects (input: Text): {Fail} List Rect := Parse.eachLine input rect

test "two rectangles" :=
  toResult (() => parseRects "3x4\n10x2\n") == Ok [{ width = 3, height = 4 }, { width = 10, height = 2 }]
test "a bad line" := toResult (() => parseRects "3x4\n10-2\n") == Err "line 2, column 3: expected 'x', got '-'"

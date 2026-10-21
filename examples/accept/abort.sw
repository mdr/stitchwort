-- `Abort` from the library: parse step by step, giving up at the first
-- step that fails, as Lean's `do` over `Option` or Roc's `?` do. Each line
-- is a direction, a distance and a colour: `L68 3 red`.
import Std.Abort (need, ensure, abort, toOption, orElse)
import Std (Abort, IO)

type Turn = { left: Bool, steps: Nat, weight: Nat, colour: Text }

def colours: List Text := ["red", "green", "blue"]

-- Each `need` reads an `Option`; a `None` stops the whole parse.
def turn (line: Text): {Abort} Turn :=
  match line.split ' ' with
    | [dir, w, colour] =>
      let (c, digits) := need dir.uncons
      ensure (c == 'L' || c == 'R')
      ensure (colours.any (k => k == colour))
      { left = c == 'L', steps = need digits.toNat, weight = w.toNat.orAbort, colour }
    | _ => abort()

-- Every line, or give up if any line is bad.
def turns: List Text -> {Abort} (List Turn)
  | []        => []
  | [l, ..ls] => Cons (turn l) (turns ls)

def parseTurn (line: Text): Option Turn := toOption (() => turn line)

-- The signed distance, with a default for a bad line. (The `0` needs its
-- type: arguments are checked before the result type is known.)
def signed (line: Text): Int :=
  orElse (0: Int) (() =>
    let t := turn line
    let n := t.steps.toInt
    if t.left then -n else n)

-- Composes with other abilities: prints each line's colour as it goes, and
-- gives up at the first bad line (after printing the good ones before it).
def total (lines: List Text): {IO, Abort} Nat :=
  match lines with
    | []        => 0
    | [l, ..ls] =>
      let t := turn l
      IO.print t.colour
      t.steps * t.weight + total ls

def main(): {IO} () :=
  let lines := IO.readAllLines()
  match toOption (() => total lines) with
    | Some n => IO.print ("total " ++ n.toText)
    | None   => IO.print "bad input"

test "a line" := parseTurn "L68 3 red" == Some { left = True, steps = 68, weight = 3, colour = "red" }
test "bad direction" := parseTurn "X68 3 red" == None
test "bad number" := parseTurn "R6x 3 red" == None
test "bad colour" := parseTurn "R6 3 pink" == None
test "too few fields" := parseTurn "R6 3" == None
test "empty line" := parseTurn "" == None
test "all lines" := toOption (() => turns ["L1 1 red", "R2 2 blue"]) == Some [{ left = True, steps = 1, weight = 1, colour = "red" }, { left = False, steps = 2, weight = 2, colour = "blue" }]
test "one bad line" := toOption (() => turns ["L1 1 red", "R2"]) == None
test "default" := signed "L5 1 red" == -5 && signed "?" == 0
test "with IO" := IO.simulate ["L2 3 red", "R1 1 blue"] (() => toOption (() => total ["L2 3 red", "R1 1 blue"])) == (["red", "blue"], Some 7)
test "with IO, then a bad line" := IO.simulate [] (() => toOption (() => total ["L2 3 red", "nope", "R1 1 blue"])) == (["red"], None)

-- The handler's result on small inputs, by computation.
theorem parsesL68: signed "L68 1 green" = -68 := rfl
theorem rejectsJunk: parseTurn "L68" = None := rfl

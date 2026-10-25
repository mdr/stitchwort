-- `Fail` from the library: parse step by step, failing at the first step
-- that goes wrong with a message that says why. Each line is a direction,
-- a distance and a colour: `L68 3 red`.
import Std.Fail (fail, need, ensure, toResult, orElse, context)
import Std (Abort, Fail, IO, List, Result)

type Turn = { left: Bool, steps: Nat, weight: Nat, colour: Text }

def colours: List Text := ["red", "green", "blue"]

-- `need` reads an `Option`, `ensure` checks a condition, and `fail` gives
-- up wherever a value is expected; each says what went wrong.
def turn (line: Text): {Fail} Turn :=
  match line.split ' ' with
    | [dir, weightText, colour] =>
      let (letter, digits) := need dir.uncons "expected a direction, got nothing"
      ensure (letter == 'L' ∨ letter == 'R') "expected L or R, got '${dir}'"
      ensure (colours.any (== colour)) "expected a colour, got '${colour}'"
      { left = letter == 'L', steps = digits.toNatOrFail, weight = weightText.toNatOrFail, colour }
    | _ => fail "expected a turn like L68 3 red, got '${line}'"

-- Every line, or the first line's failure, with its line number in front.
def turns (lines: List Text): {Fail} (List Turn) :=
  List.zip (List.range lines.length) lines |> .map (p =>
    context "line ${p.fst + 1}" (() => turn p.snd))

def parseTurn (line: Text): Result Turn Text := toResult (() => turn line)

-- The signed distance, with a default for a bad line.
def signed (line: Text): Int :=
  orElse 0 (() =>
    let turned := turn line
    let n := turned.steps.toInt
    if turned.left then -n else n)

-- Composes with other abilities: prints each line's colour as it goes, and
-- fails at the first bad line (after printing the good ones before it).
def total (lines: List Text): {IO, Fail} Nat :=
  match lines with
    | [] => 0
    | [line, ..rest] =>
      let turned := turn line
      IO.print turned.colour
      turned.steps * turned.weight + total rest

-- A whole number, or `-1`: the fallback is checked as an `Int`, the type
-- the whole call is expected to have.
def intOrMinusOne (text: Text): Int := orElse (-1) (() => text.toIntOrFail)

def main(): {IO} () :=
  let lines := IO.readAllLines()
  match toResult (() => total lines) with
    | Ok n => IO.print "total ${n}"
    | Err msg => IO.print "error: ${msg}"

test "a line" := parseTurn "L68 3 red" == Ok ({ left = True, steps = 68, weight = 3, colour = "red" })
test "bad direction" := parseTurn "X68 3 red" == Err "expected L or R, got 'X68'"
test "bad number" := parseTurn "R6x 3 red" == Err "expected a whole number, got '6x'"
test "bad colour" := parseTurn "R6 3 pink" == Err "expected a colour, got 'pink'"
test "too few fields" := parseTurn "R6 3" == Err "expected a turn like L68 3 red, got 'R6 3'"
test "empty direction" := parseTurn " 3 red" == Err "expected a direction, got nothing"
test "all lines" := toResult (() => turns ["L1 1 red", "R2 2 blue"]) == Ok [{ left = True, steps = 1, weight = 1, colour = "red" }, { left = False, steps = 2, weight = 2, colour = "blue" }]
test "one bad line" := toResult (() => turns ["L1 1 red", "R2"]) == Err "line 2: expected a turn like L68 3 red, got 'R2'"
test "default" := signed "L5 1 red" == -5 ∧ signed "?" == 0
test "a number or minus one" := intOrMinusOne "12" == 12 ∧ intOrMinusOne "x" == -1
test "with IO" := IO.simulate [] (() => toResult (() => total ["L2 3 red", "R1 1 blue"])) == (["red", "blue"], Ok 7)
test "with IO, then a bad line" := IO.simulate [] (() => toResult (() => total ["L2 3 red", "nope", "R1 1 blue"])) == (["red"], Err "expected a turn like L68 3 red, got 'nope'")
test "Abort to Fail" := toResult (() => Abort.orFail "no digits" (() => Abort.need "x".toNat)) == (Err "no digits": Result Nat Text)

-- The handler's result on small inputs, by computation.
theorem parsesL68: signed "L68 1 green" = -68 := rfl
theorem rejectsJunk: parseTurn "L68" = Err "expected a turn like L68 3 red, got 'L68'" := rfl

-- The dial from Advent of Code 2025, day 1: a safe dial numbered 0 to 99
-- starts at 50 and is turned left or right. Turning left from 0 lands on 99,
-- so the position wraps, which `Int.modNat` does for negative numbers too.

type Turn =
  | Left (clicks: Nat)
  | Right (clicks: Nat)

-- A position is a number together with a proof that it is on the dial.
type Pos = { at: Nat, ok: at < 100 }

-- Wrapping any integer onto the dial. `Int.modNatLt` is the proof; the
-- divisor 100 is not zero, so that argument is filled in automatically.
def wrap (x: Int): Pos := { at = Int.modNat x 100, ok = Int.modNatLt x 100 }

def start: Pos := wrap 50

def turn (p: Pos): Turn -> Pos
  | Left n  => wrap (Nat.toInt p.at - Nat.toInt n)
  | Right n => wrap (Nat.toInt p.at + Nat.toInt n)

-- Turn through the whole list, counting each time the dial lands on 0. The
-- accumulator is the position and the count so far.
def step: (Pos, Nat) -> Turn -> (Pos, Nat)
  | (p, count), t => tally (turn p t) count

def tally (q: Pos) (count: Nat): (Pos, Nat) := (q, if q.at == 0 then count + 1 else count)

def zeros (ts: List Turn): Nat := (ts.foldLeft step (start, 0)).snd

-- The sample from the puzzle: L68 L30 R48 L5 R60 L55 L1 L99 R14 L82.
def sample: List Turn := [Left 68, Left 30, Right 48, Left 5, Right 60, Left 55, Left 1, Left 99, Right 14, Left 82]

test "sample password is 3" := zeros sample == 3

test "L68 from 50 lands on 82" := (turn start (Left 68)).at == 82
test "L1 from 0 lands on 99" := (turn (wrap 0) (Left 1)).at == 99
test "R1 from 99 lands on 0" := (turn (wrap 99) (Right 1)).at == 0
test "a full turn changes nothing" := (turn start (Right 100)).at == 50

theorem wrapNegative: Int.modNat (-18) 100 = 82 := rfl

-- Every position is below 100, from the proof stored in the record, and
-- also straight from the lemma.
theorem onDial (x: Int): Int.modNat x 100 < 100 := Int.modNatLt x 100

-- The `Nat` position and the integer remainder are the same number.
theorem sameNumber (x: Int): Nat.toInt (Int.modNat x 100) = x % 100 := Int.modNatToInt x 100

-- Division and remainder rebuild the number, even for a negative divisor.
theorem rebuild (x: Int): -7 * (x / -7) + x % -7 = x := Int.divAddMod x (-7)

-- `Mod n`: numbers that wrap around, as on a clock. `+` and `*` come from the
-- `Add` and `Mul` instances; `Mod.sub` and `Mod.neg` are named functions.
import Std (IO, Int, List, Mod, Fin)

-- A dial numbered 0 to 99 that starts at 50 (Advent of Code 2025, day 1),
-- turned by these amounts (left is negative): how many turns end on 0?
def turns: List Int := [-68, -30, 48, -5, 60, -55, -1, -99, 14, -82]

def zeros (turns: List Int): Nat :=
  turns
    |> .scanLeft (Mod.ofNat 50: Mod 100) (p t => p + Mod.ofInt t)
    |> .drop 1
    |> .count (p => p == Mod.ofNat 0)

test "the dial" := zeros turns == 3

test "positions" :=
  (turns.scanLeft (Mod.ofNat 50: Mod 100) (p t => p + Mod.ofInt t)).map (p => p.value)
    == [50, 82, 52, 0, 95, 55, 0, 99, 0, 14, 32]

def main(): {IO} () := IO.print "zeros: ${zeros turns}"

-- Wrapping: `+` and `*` reduce, `Mod.ofNat` and `Mod.ofInt` wrap into range.
def c: Mod 100 := Mod.ofNat 150
theorem wraps: c = Mod.ofNat 50 := rfl
theorem wrapsAdd: (Mod.ofNat 99: Mod 100) + Mod.ofNat 1 = Mod.ofNat 0 := rfl
theorem wrapsMul: (Mod.ofNat 30: Mod 100) * Mod.ofNat 7 = Mod.ofNat 10 := rfl
theorem wrapsInt: (Mod.ofInt (-1): Mod 100) = Mod.ofNat 99 := rfl

-- Subtraction wraps too, where `Nat`'s `5 - 7` is 0. `i.sub j` is `i - j`.
theorem subWraps: (Mod.ofNat 5: Mod 100).sub (Mod.ofNat 7) = Mod.ofNat 98 := rfl
theorem negWraps: (Mod.ofNat 30: Mod 100).neg = Mod.ofNat 70 := rfl

-- `Mod 0` has one value, 0.
theorem modZero: (Mod.ofNat 5: Mod 0) = Mod.ofNat 0 := rfl

-- The laws `+` and `*` carry, for every modulus: through the interface.
theorem addComm (i: Mod 7) (j: Mod 7): i + j = j + i := Add.comm i j
theorem mulAssoc (i: Mod 7) (j: Mod 7) (k: Mod 7): (i * j) * k = i * (j * k) := Mul.assoc i j k
theorem subSelf (i: Mod n): i.sub i = Mod.zero := Mod.subSelf i

-- The range proof is decided, not built from `Nat.modLt`, so checking an `rfl`
-- at a large modulus is quick (with `Nat.modLt` this ran out of resources).
theorem bigWrap: (Mod.ofNat 1000001: Mod 1000000) = Mod.ofNat 1 := rfl
theorem bigValue: (Mod.ofNat 1000001: Mod 1000000).value = 1 := rfl
theorem bigAdd: (Mod.ofNat 999999: Mod 1000000) + Mod.ofNat 2 = Mod.ofNat 1 := rfl

-- Conversions with `Fin`, the type of positions in a `Vec`.
theorem finRound: ((Fin.ofNat 3: Fin 5).toMod).value = 3 := rfl
test "toFin" := Fin.toNat (Mod.toFin (Mod.ofNat 7: Mod 5)) == 2
test "== and <" := (Mod.ofNat 3: Mod 5) < Mod.ofNat 4 ∧ (Mod.ofNat 8: Mod 5) == Mod.ofNat 3
test "show" := "${(Mod.ofNat 207: Mod 100)}" == "7"

-- expect-error: E-UNIVERSE
-- `if h:` can't choose between proofs yet either (SW-373). The note
-- suggests matching on the condition's decision procedure, named, which
-- keeps `h` in each branch (SW-933):
-- `match Std.Nat.decLessThan m (List.length rest) with | Yes h => … | No h => …`.
import Std (List)

theorem choose (m: Nat) (rest: List Nat): 0 = 0 := if h: m < List.length rest then rfl else rfl

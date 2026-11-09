-- Number patterns on a `Fin` are compiled as numbers: one subtree for each
-- number written, and one for the rest, however far apart the numbers are.
-- The kernel still matches a `Fin` one `FSucc` at a time, up to the
-- largest number written (docs/proposals/fin-literals.md).
import Std (Fin)

def size: (n: Nat) → Fin (Succ (Succ n)) → Text
  | _, 0 => "none"
  | _, 12 => "twelve"
  | _, _ => "some"

theorem sizeZero: size 20 0 = "none" := rfl
theorem sizeTwelve: size 20 12 = "twelve" := rfl
theorem sizeOther: size 20 11 = "some" := rfl

-- A number above the limit for patterns (64) is compared in a condition.
def far: (n: Nat) → Fin (Succ (Succ n)) → Text
  | _, 0 => "none"
  | _, i if i.toNat == 1000000 => "a million"
  | _, _ => "some"

test "a million" := far 1000000 1000000 == "a million"
test "one less" := far 1000000 999999 == "some"

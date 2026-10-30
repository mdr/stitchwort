-- `cases`' decision closer (docs/proposals/decide.md §6.1.2): a case that no
-- other closer proves, with nothing left to split, is closed by running the
-- goal's decision procedure, as `auto` does, when it says `Yes`. The proof
-- is `auto`'s, `Decidable.fromYes d Trivial`, which the kernel runs again.
import Std (Bool, List, Nat, Void)

type Key =
  | K0
  | K1
  | K2

def keys: List Key := [K0, K1, K2]

-- A closed membership: nothing to split, and neither computation nor
-- `omega` proves a disjunction of equations of keys.
theorem inKeys: K1 ∈ keys := cases

-- `Decidable.or` decides left to right: a left side that decides `Yes` is
-- enough, with the right side stuck on `flag`.
theorem leftYes (flag: Bool): Or (K1 ∈ keys) (flag = True) := cases

-- A leaf closed only by deciding, after a split: `pick b` is stuck on `b`,
-- and in each case the membership decides.
def pick (b: Bool): Key := if b then K2 else K0

theorem pickIn (b: Bool): pick b ∈ keys := cases

-- A goal that decides `No`, in a case whose hypotheses contradict each
-- other: `No` doesn't fail the case, and `omega` refutes `h`
-- (examples/accept/cases-pi-goals.sw pins its hash).
theorem falseGoalImpossibleCase (n: Nat) (h: n + 1 < n): 2 ∈ [1, 3] := cases

-- `byDecision` (docs/proposals/decide.md §2, §6.2): a closed decidable
-- statement, proved by running its decision procedure. It is `auto` under a
-- name: the proof is `Decidable.fromYes d Trivial`, which the kernel checks
-- by running `d` again. A false one is `E-AUTO-FALSE`.
import Std (byDecision, List, Nat)

type Key =
  | Digit0
  | Digit1
  | Digit2
  | Enter

def keys: List Key := [Digit0, Digit1, Digit2, Enter]

theorem enterIn: Enter ∈ keys := byDecision

theorem twoTwos: 2 + 2 < 5 := byDecision

theorem notThree: Not (Digit1 = Digit2) := byDecision

theorem either: Or (Digit2 ∈ keys) (3 = 4) := byDecision

-- Every key, closed by deciding each case once `cases` has split it.
theorem everyKey (key: Key): key ∈ keys := cases

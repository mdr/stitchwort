-- expect-error: E-TYPE-MISMATCH
-- expect-warning: W-REWRITE-UNCONFIRMED
-- A `rewrite` that could only look at the goal as written (its unfolding is
-- too large) still proves only what its rule says: the goal becomes
-- `q (Some y)`, which `h` doesn't prove. (examples/accept/as-written-unconfirmed.sw)
import Std (Bool, Eq, Nat, Option)

def step (n: Nat) (k: Nat): Nat := n * k + 1

def settle (x: Nat) (k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step x k
    if next == x then Some x else settle next k more

def limit: Nat := 1000

theorem wrongValue (x: Nat) (k: Nat) (y: Nat) (settles: settle x k limit = Some y)
    (q: Option Nat → Prop) (h: q (Some 0)): q (settle x k limit) :=
  rewrite settles in h

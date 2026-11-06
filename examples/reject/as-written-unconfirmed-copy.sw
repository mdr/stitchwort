-- expect-error: E-TYPE-MISMATCH
-- A `rewrite` that could only look at the goal as written (its unfolding is
-- too large) leaves a copy of the left side hidden inside a call. That never
-- makes a wrong proof check: the next step fails, here the body `h`, which
-- needs the copy inside `settled` rewritten too.
-- (examples/accept/as-written-unconfirmed.sw) The
-- `rewrite` fails as a whole, so its `W-REWRITE-UNCONFIRMED` is dropped
-- with what it did.
import Std (Bool, Eq, Nat, Option)

def step (n: Nat) (k: Nat): Nat := n * k + 1

def settle (x: Nat) (k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step x k
    if next == x then Some x else settle next k more

def limit: Nat := 1000

def settled (x: Nat) (k: Nat): Option Nat := settle x k limit

theorem hiddenCopy (x: Nat) (k: Nat) (y: Nat) (settles: settle x k limit = Some y)
    (q: Option Nat → Option Nat → Prop) (h: q (Some y) (Some y)): q (settle x k limit) (settled x k) :=
  rewrite settles in h

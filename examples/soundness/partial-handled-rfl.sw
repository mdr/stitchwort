-- expect-error: E-REFL
-- The checker never runs a handled partial program
-- (docs/proposals/partial-handlers.md §3.3): `foldD`, the handler fold for
-- partial code, has no computation rule, so `caught 5` stops at `foldD …`
-- and isn't `Err "three"`, even though it finishes with it.
import Std (Empty, Fail)

def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)

def caught (n: Nat): {Partial} Result Nat Text :=
  handle countdown n with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

def settled (n: Nat): {Partial} Result Nat Text := Err "three"

theorem same: ((u => caught 5): () → {Partial} Result Nat Text) = (u => settled 5) := rfl

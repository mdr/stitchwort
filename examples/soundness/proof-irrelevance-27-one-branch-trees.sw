-- expect-error: E-REFL
-- Two `case`s with no possible branch are equal without comparing their
-- scrutinees, but a `case` with one still compares them. Partner:
-- `absurdTransitive` in accept/proof-irrelevance.sw.
import Std (Nat)

type Tok: Prop =
  | MkTok

def tokA (t: Tok): Nat :=
  match t with
    | MkTok => 0

def tokB (t: Tok): Nat :=
  match t with
    | MkTok => 0

theorem t27 (t: Tok) (t2: Tok): tokA t = tokB t2 := rfl

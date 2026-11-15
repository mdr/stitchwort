-- expect-error: E-TERMINATION
-- proof-irrelevance-07's descent with the one field's type `p n`, for a
-- parameter `p: Nat → Prop`: whatever `p` is, the field is a proof (its
-- type's sort is `Prop`), so it can't carry the wrapper rule's descent
-- (docs/reviews/SW-3412-text-rest-relanded.md, a2).
import Std (Nat, Void)
type Loop: Prop = | MkLoop (next: Loop)
type BoxF (p: Nat → Prop) (n: Nat): Type = | MkBoxF (h: p n)
def f (b: BoxF (_ => Loop) 0): Void := match b with
  | MkBoxF l =>
    match l with
      | MkLoop n => f (MkBoxF n)

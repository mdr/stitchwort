-- expect-error: E-TERMINATION
-- Agda #8699's descent (soundness/proof-irrelevance-07) with the
-- proposition behind a definition: `MyP` unfolds to `Loop`, so `MkBox2`'s
-- one field is a proof, and `MkBox2 n` is the same value as `b` to the
-- kernel. Whether a field is a proof is read from its declared type, up to
-- unfolding (docs/reviews/SW-3412-text-rest-relanded.md, a1).
import Std (Void)
type Loop: Prop = | MkLoop (next: Loop)
def MyP: Prop := Loop
type Box2: Type = | MkBox2 (h: MyP)
def f (b: Box2): Void := match b with
  | MkBox2 l =>
    match l with
      | MkLoop n => f (MkBox2 n)

-- expect-error: E-REFL
-- Rule S on a proof field bound by an enclosing match reads the field's
-- type off its declaration, over the enclosing scrutinee's parameters and
-- earlier fields, and takes the branch only when its indices are the
-- constructor's. `q: Q2 1`, which `MkQ2` can't build, stays stuck (the
-- branch would run under the false refinement `1 = 0`), as does `q: Q2 b.n`
-- in an unknown record `b`, which record eta takes apart.
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0

type Around (k: Nat): Prop = | MkAround (q: Q2 k)

def ga (k: Nat): Around k → Nat
  | MkAround q =>
    match q with
      | MkQ2 w => 7

theorem apart ∀ (o: Around 1): ga 1 o = 7 := byComputing

type Box = { n: Nat, q: Q2 n }

def gb: Box → Nat
  | { n, q } =>
    match q with
      | MkQ2 w => 3

theorem unknown ∀ (b: Box): gb b = 3 := byComputing

-- expect-error: E-REFL
-- Rule S on an indexed proposition whose constructor has a proof field
-- (D3727) takes the branch only when the scrutinee's indices equal the
-- constructor's: then the constructor applied to the proof's fields has the
-- proof's type, and the refinement the branch was checked under holds. At
-- `1`, which `MkQ2` can't build, taking the branch would run it under the
-- false refinement `1 = 0` (no type preservation), so the match stays
-- stuck.
import Std (Eq, Nat)

type Q2: Nat → Prop = | MkQ2 (w: 0 = 0): Q2 0

def f (x: Nat): Q2 x → Nat
  | MkQ2 w => 5

theorem apart ∀ (s: Q2 1): f 1 s = 5 := byComputing

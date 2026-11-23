-- expect-error: E-REFL
-- Two proofs of one family, only the first with equal indices: rule S reads
-- the type of the proof matched, so the match on the second stays stuck.
import Std (Nat)

type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

def second (x y: Nat) (h1: Same Nat x x) (h2: Same Nat x y) (n: Nat): Nat := match h2 with | MkSame => n

theorem mustRefuse ∀ (x y: Nat) (h1: Same Nat x x) (h2: Same Nat x y): second x y h1 h2 4 = 4 := byComputing

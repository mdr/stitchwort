-- expect-error: E-REFL
-- Rule S takes the branch of a match on an indexed proposition only when its
-- constructor's result indices equal the scrutinee's (D3724): here `x` and
-- `y` may differ, and the branch was checked with `y` replaced by `x`, so the
-- match stays stuck. Partner: `carryAny` in accept/rules-k-and-s.sw.
import Std (Nat)

type Same (a: Type) (x: a): a → Prop = | MkSame: Same a x x

def carry (x y: Nat) (h: Same Nat x y) (n: Nat): Nat := match h with | MkSame => n

theorem carryApart ∀ (x y: Nat) (h: Same Nat x y): carry x y h 4 = 4 := byComputing

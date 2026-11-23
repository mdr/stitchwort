-- expect-error: E-REFL
-- A heterogeneous equation has two indices, and rule S needs both to agree:
-- `HEq a x a y` with `x` and `y` unknown stays stuck.
import Std (Nat)

type HEq (a: Type) (x: a): (b: Type) → b → Prop = | HRefl: HEq a x a x

def hcast (a b: Type) (x: a) (y: b) (h: HEq a x b y) (n: Nat): Nat := match h with | HRefl => n

theorem mustRefuse ∀ (a: Type) (x y: a) (h: HEq a x a y): hcast a a x y h 3 = 3 := byComputing

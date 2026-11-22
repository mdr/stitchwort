-- `auto` closes an equation whose two sides are the same term, even when
-- the decision procedure for the equation is stuck on a variable.
type T = | C (t: T) | Blank

def blank (t: T): T := match t with
  | C inner => C (blank inner)
  | Blank => Blank

theorem lem ∀ [g g2: T → T] (t: T) [auto same: g2 (blank t) = blank (g t)]: g2 (blank t) = blank (g t) := same

theorem use ∀ (t: T): C (blank t) = C (blank t) := lem [g := C] [g2 := C] t

-- A guard that refines a proof's goal copies the variables whose types
-- mention its condition; the guarded arm and the arms below name the
-- copies, as a `match`'s arms do (SW-4391). Here `w` is the copy of `v`,
-- whose length is `1` in the guarded arm and `2` below, the same vector as
-- the goal's.

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def pick (b: Bool): Nat := if b then 1 else 2

theorem same ∀ (k: Nat) (v: Vec Nat k): v = v := byComputing

theorem copiedInBothArms ∀ (n: Nat) (b: Bool) (v: Vec Nat (pick b)): v = v := match n, v with
  | 0, w if b => same _ w
  | _, w => same _ w

theorem copiedBelow ∀ (n: Nat) (b: Bool) (v: Vec Nat (pick b)): v = v := match n, v with
  | 0, _ if b => byComputing
  | _, w => same _ w

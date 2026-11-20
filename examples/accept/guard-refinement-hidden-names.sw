-- The arms below a guard don't see the names its arm bound, even where the
-- guard refined the goal and those names came to mean copies (SW-4391): `e`
-- below is the theorem's `e`, not the guarded arm's, which named `v`.

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def pick (b: Bool): Nat := if b then 1 else 2

theorem same ∀ (k: Nat) (v: Vec Nat k): v = v := byComputing

-- The outer `e` is copied too, its type mentioning `b`.
theorem outerCopied ∀ (n: Nat) (b: Bool) (v: Vec Nat (pick b)) (e: Vec Nat (pick b + 1)): e = e := match n, v with
  | 0, e if b => byComputing
  | _, _ => same _ e

theorem outerKept ∀ (n: Nat) (b: Bool) (v: Vec Nat (pick b)) (e: Vec Nat 3): v = v ∧ e = e := match n, v with
  | 0, e if b => (byComputing, byComputing)
  | _, _ => (same _ v, same _ e)

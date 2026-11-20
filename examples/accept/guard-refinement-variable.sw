-- A guard whose condition is a `Bool` variable the arms below don't split,
-- where refining by generalising the condition fails, is split where it
-- is, as `match` splits a variable (SW-4391): in the guarded arm `flag` is
-- `True` wherever it appears, under any name, and below it `False`. Here
-- `pick flag` is written in the arms: generalised, `v`'s copy has length
-- `pick True` but the term names `flag`.

type Vec (a: Type): Nat → Type =
  | VNil: Vec a 0
  | VCons (x: a) (xs: Vec a n): Vec a (Succ n)

def pick (b: Bool): Nat := if b then 1 else 2

theorem same ∀ (k: Nat) (v: Vec Nat k): v = v := byComputing

theorem byName ∀ (n: Nat) (flag: Bool) (v: Vec Nat (pick flag)): v = v := match n with
  | 0 if flag => same (pick flag) v
  | _ => same (pick flag) v

-- Generalising `flag` is enough here, so that is how this one refines.
theorem belowFalse ∀ (flag: Bool): pick flag = 1 ∨ flag = False := match flag with
  | f if g: f => Inl byComputing
  | _ => Inr byComputing

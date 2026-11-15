-- SW-3344: `cases` takes a hypothesis `C a = C b` apart into `a = b`, and
-- when a side of that is a variable, puts the other side in its place in the
-- goal and in the hypotheses that mention it, then goes on. Before, it added
-- `x = y` and stopped, so even `f x = f y` stayed open.
import Std (Bool, Fin, List, Nat, Option)

type Outcome (a: Type) = | Stable (value: a) | Refused

type Shape = | Dot (x: Nat) | Box (x: Nat) (y: Nat) (label: Bool)

-- One field: `y` is replaced by `x`, and the goal computes.
theorem stableCong ∀ (f: Nat → Bool) (x y: Nat) (h: Stable x = Stable y): f x = f y := cases

-- A side that isn't a variable: `x` is replaced by `3`.
theorem toLiteral ∀ (x: Nat) (h: Some 3 = Some x): x * 2 = 6 := cases

-- Several fields, each its own equation.
theorem severalFields ∀ (f: Nat → Nat → Bool → Nat) (a b c d: Nat) (p q: Bool)
    (h: Box a b p = Box c d q):
    f a b p = f c d q :=
  cases

-- Nested: `Some x = Some y` first, then `x = y`.
theorem nested ∀ (f: Nat → Nat) (x y: Nat) (h: Some (Some x) = Some (Some y)): f x = f y := cases

-- The variable is replaced under a binder too.
theorem underBinder ∀ (xs: List Nat) (x y: Nat) (h: Some x = Some y): xs.map (z => z + x) = xs.map (z => z + y) := cases

-- A hypothesis that mentions the variable is copied with the other side.
theorem carriesHypothesis ∀ (p: Nat → Bool) (x y: Nat) (h: Some x = Some y) (hy: p y = True): p x = True := cases

-- So is a variable whose type mentions it: `i: Fin m` becomes `i: Fin n`,
-- and the term after `in` names the copy.
theorem dependentType ∀ (n m: Nat) (i: Fin m) (h: Some n = Some m): Fin.toNat i < n := cases in Fin.toNatLt i

-- `omega` sees `f x` and `f y` as one number once `y` is replaced.
theorem thenOmega ∀ (f: Nat → Nat) (x y: Nat) (k: f y = 7) (h: Some x = Some y): f x + 1 = 8 := cases

-- The replaced variable's name stands for what replaced it, so a term after
-- `in` that names `y` still checks after `y` became `x` (in the case `b =
-- False`, where `lem … y hy` is checked against `p x`).
def k (b: Bool) (n: Nat): Nat := if b then n else n

theorem lem ∀ (p q: Nat → Prop) (step: ∀ (m: Nat) => q m → p m) (n: Nat) (hn: q n): p n := step n hn

theorem namesReplaced ∀ (p q: Nat → Prop) (step: ∀ (m: Nat) => q m → p m) (b: Bool) (x y: Nat)
    (h: Some x = Some y) (hy: q y):
    p (k b y) :=
  cases in lem p q step y hy

-- `auto` uses a test fact in scope as the proposition it reads as
-- (docs/proposals/bool-as-proposition.md §9): `(a && b) = True` gives `a`
-- and `b`, `(a || b) = False` gives `a = False` and `b = False`, and each
-- of those is read again, so `(p == q) = False` gives `p ≠ q` and
-- `o.isSome = False` gives `o = None`. A `∀` it reads as, such as `xs.all
-- p`'s, is applied to a member in scope.
import Std (Bool, List, Nat, Option)

type Point = { x: Nat, y: Nat }

def present (x: Nat) (xs: List Nat) [auto ok: x ∈ xs]: Nat := x

def apart (p q: Point) [auto ok: p ≠ q]: Nat := p.x + q.x

def none (o: Option Nat) [auto ok: o = None]: Nat := 0

def small (x: Nat) [auto ok: x < 5]: Nat := x

-- `(a && b) = True`: each side.
def inBoth (x: Nat) (xs ys: List Nat) (h: (xs.contains x && ys.contains x) = True): Nat := present x xs + present x ys

test "in both" := inBoth 2 [1, 2] [2, 3] (Both rfl rfl) == 4

-- The equation a `match` gives its branch.
def whenWanted (x: Nat) (xs: List Nat) (wanted: Bool): Nat := match ok: wanted && xs.contains x with
  | True => present x xs
  | False => 0

test "when wanted" := whenWanted 2 [1, 2] True == 2 ∧ whenWanted 2 [1, 2] False == 0

-- `(a || b) = False`: each side is `False`, read again.
def different (p q: Point) (h: (p == q || p.x == 0) = False): Nat := apart p q

test "different" := different { x = 1, y = 2 } { x = 3, y = 4 } rfl == 4

def empty (o: Option Nat) (h: o.isSome = False): Nat := none o

test "empty" := empty None rfl == 0

-- `xs.all p = True` reads as `∀ (x: Nat) => x ∈ xs → p x`, applied to `y`
-- with its membership `m`.
def member (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: xs.all (x => x < 5) = True): Nat := small y

test "member" := member [1, 4] 4 (Inr (Inl rfl)) rfl == 4

def checked (xs: List Nat) (y: Nat) (m: y ∈ xs): Nat := match ok: xs.all (x => x < 5) with
  | True => small y
  | False => 0

test "checked" := checked [1, 4] 4 (Inr (Inl rfl)) == 4 ∧ checked [1, 7] 1 (Inl rfl) == 0

-- The same `∀`, given as a proposition.
def given (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: ∀ (x: Nat) => x ∈ xs → x < 5): Nat := small y

-- A rule whose conclusion is itself a negation: `x ≠ 0` is `x = 0 → Void`,
-- and the rule is applied to `y` and `m` only, not past the `≠`.
def nonzero (d: Nat) [auto ok: d ≠ 0]: Nat := d

def divisor (xs: List Nat) (y: Nat) (m: y ∈ xs) (h: ∀ (x: Nat) => x ∈ xs → x ≠ 0): Nat := nonzero y

-- On a type known only to have `==`, a fact about it reads by its
-- decision: `(a == b) = False` gives `a ≠ b` through `Decidable.refute`.
def distinct [auto eq: DecEq k] (a b: k) [auto ok: a ≠ b]: Nat := 0

def unequal [auto eq: DecEq k] (a b: k) (h: (a == b) = False): Nat := distinct a b

-- A cons list's `all` reads as `∧` (`d < 5` and `more.all p`) and also as the
-- `∀`, so `auto` still finds `small y` from a member, whether the list was
-- matched or written as a cons.
def afterMatch (xs: List Nat) (h: xs.all (x => x < 5)) (y: Nat) (m: y ∈ xs): Nat := match xs with
  | [] => 0
  | [d, ..more] => small y

def fromCons (d: Nat) (more: List Nat) (h: [d, ..more].all (x => x < 5)) (y: Nat) (m: y ∈ [d, ..more]): Nat := small y

test "after match" := afterMatch [1, 4] (Both rfl (Both rfl rfl)) 4 (Inr (Inl rfl)) == 4

-- Where a test fact is expected, a proof of what it reads as is accepted:
-- the compiler builds the fact through the reading (D3549a,
-- docs/proposals/bool-as-proposition-building.md).
import Std (Bool, Eq, List, Nat)

-- A membership proof where `xs.contains x` is expected: as the body, in a
-- typed `let`, as a lemma's argument and inside a constructor.
theorem fromMember (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x := m

theorem inLet (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x :=
  let found: xs.contains x := m
  found

theorem useFound (x: Nat) (xs: List Nat) (found: xs.contains x): xs.contains x := found

theorem asArgument (x: Nat) (xs: List Nat) (m: x ∈ xs): xs.contains x := useFound x xs m

theorem insideBoth (x: Nat) (xs: List Nat) (m: x ∈ xs) (small: x < 3): (xs.contains x && x < 3) = True :=
  Both m small

theorem insideInl (x: Nat) (xs: List Nat) (m: x ∈ xs) (b: Bool): (xs.contains x || b) = True := Inl m

theorem insideWitness (xs ys: List Nat) (inYs: 2 ∈ ys) (inXs: 2 ∈ xs): ys.any (y => xs.contains y) :=
  Witness 2 (Both inYs inXs)

-- Equations at `Nat`: `x = y` is what `(x == y) = True` reads as.
theorem fromEqual (x y: Nat) (same: x = y): (x == y) = True := same

theorem fromApart (x y: Nat) (ne: x ≠ y): (x == y) = False := ne

-- Two layers: `!=` reads as `(a == b) = False`, which reads as `a ≠ b`.
theorem fromApartBang (a b: Nat) (ne: a ≠ b): ((a != b): Bool) = True := ne

theorem fromApartLambda (a: Nat) (b: Nat) (lower: a < b): ((a != b): Bool) = True := same => omega

-- A lambda takes the binders of the reading it is checked against.
theorem allSmall (xs: List Nat) (small: ∀ (x: Nat) => x ∈ xs → x < 10): xs.all (x => x < 10) :=
  x inXs => small x inXs

theorem notZero (n: Nat) (big: n > 3): Nat.equal n 0 = False := isZero => omega

-- A negative reading: `<=` that is `False` reads as `<` the other way.
theorem fromLess (m n: Nat) (less: n < m): (m <= n) = False := less

-- A test with no negative reading is built from the plain `¬(e = True)`.
def isWall (n: Nat): Bool := n % 7 == 3

theorem notWall (n: Nat) (no: ¬(isWall n = True)): isWall n = False := no

theorem notLeq (a b: Nat) (no: ¬(a ≤ b)): Nat.leq a b = False := no

-- Five built in one theorem: each failure adds a place, and the theorem is
-- checked again with every fact built so far.
theorem fiveBuilt (x y: Nat) (xs: List Nat) (m: x ∈ xs) (same: x = y) (ne: x ≠ 4) (less: y < x + 1) (no: ¬(isWall x = True)):
    xs.contains x ∧ (x == y) = True ∧ ((x != 4): Bool) = True ∧ (x + 1 <= y) = False ∧ isWall x = False :=
  Both m (Both same (Both ne (Both less no)))

-- `==` on a type with a derived `DecEq` reads as `=`, and `= False` as `≠`:
-- deriving also makes the readings `T.%sameReads` and `T.%sameReadsFalse` of
-- its test `T.%same`, so a fact `(c == d) = True` is taken apart, built and
-- read as `c = d` with `.read` (docs/syntax.md, Readings). A record's `==`
-- reads as `x = y`, not as the conjunction of its fields.
import Std (Bool, Eq, Nat)

type Dir = | North | East | Turn (by: Nat)

type Point = { x: Nat, y: Nat }

type Box (a: Type): Type = | Empty | Full (item: a)

theorem sameDir ∀ (c d: Dir) (h: (c == d) = True): c = d := h.read

theorem apartDir ∀ (c d: Dir) (h: (c == d) = False): c ≠ d := h.read

theorem apartDirApplied ∀ (c d: Dir) (h: (c == d) = False) (e: c = d): Void := h.read e

theorem swapDir ∀ (c d: Dir) (h: (c == d) = True): d = c := Eq.sym h.read

theorem samePoint ∀ (p q: Point) (h: (p == q) = True): p = q := h.read

theorem apartPoint ∀ (p q: Point) (h: (p == q) = False): p ≠ q := h.read

theorem swapPoint ∀ (p q: Point) (h: (p == q) = True): q = p := Eq.sym h.read

theorem sameBox ∀ (a: Type) [auto decEq: DecEq a] (c d: Box a) (h: (c == d) = True): c = d := h.read

theorem apartBox ∀ (a: Type) [auto decEq: DecEq a] (c d: Box a) (h: (c == d) = False): c ≠ d := h.read

-- The decision's own `==` still computes: reading is only for a test that is stuck.
theorem computes: (Turn 3 == Turn 3) = True := rfl

-- A function written before the use is read through what it unfolds to.
def sameHeading (c d: Dir): Bool := c == d

theorem viaFunction ∀ (c d: Dir) (h: sameHeading c d = True): c = d := h.read

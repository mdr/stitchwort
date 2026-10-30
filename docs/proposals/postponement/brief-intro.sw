-- The examples of "Stitchwort in brief" in review-brief.md, all accepted
-- (30 Oct 2026):
--
--   $ stitchwort test docs/proposals/postponement/brief-intro.sw

import Std (Bool, List, Nat)

-- A record type, a record literal, and `.field`.
type Point = { x: Nat, y: Nat }

def origin: Point := { x = 0, y = 0 }

def shift (p: Point) (dx: Nat): Point := { x = p.x + dx, y = p.y }

-- `a` is used only as a type, so it is an implicit parameter, filled in
-- at each call by unification: here `a` is `Point`.
def twice (f: a -> a) (v: a): a := f (f v)

def moved: Point := twice (p => shift p 1) origin

-- `let`: the value is inferred, then the body is checked.
def area (p: Point): Nat :=
  let w := p.x
  w * p.y

def apply (f: a -> b) (v: a): b := f v

-- `.field` on a parameter whose type is unknown where it is reached: the
-- lambda is tried in place, fails, and is checked again after `p`.
def xOf (p: Point): Nat := apply (q => q.x) p

test "moved twice" := moved.x == 2

test "area" := area { x = 3, y = 4 } == 12

test "xOf" := xOf moved == 2

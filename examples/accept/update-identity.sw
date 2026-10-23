-- Record and variant updates are compared by what they do (SW-386, D1091):
-- two updates written in different places are the same value, so a lemma
-- about one applies to the other.

import Std (List, Nat, Option, Vec)

type Shape =
  | Dot (ref: Nat) (id: Nat) (start: Nat)
  | Circle (ref: Nat) (id: Nat) (start: Nat) (radius: Nat)

-- 1. The same update written in two definitions.
def setId (c: Shape) (x: Nat): Shape := { c | id = x }
def setIdAgain (c: Shape) (x: Nat): Shape := { c | id = x }

theorem sameUpdate (c: Shape) (x: Nat): setId c x = setIdAgain c x := rfl

theorem idRead (c: Shape) (x: Nat): ({ c | id = x }).id = x :=
  match c with
    | Dot _ _ _ => rfl
    | Circle _ _ _ _ => rfl

-- The lemma, used for a separately written update.
theorem idReadAgain (c: Shape) (x: Nat): (setIdAgain c x).id = x := idRead c x

-- 2. The lemma at `x := double y`.
def double (n: Nat): Nat := n + n

theorem idReadDouble (c: Shape) (y: Nat): ({ c | id = double y }).id = double y :=
  idRead c (double y)

-- 3. Renamed binders and an unused local: still the same update.
def setIdRenamed (shape: Shape) (value: Nat): Shape :=
  let ignored := value + 1
  { shape | id = value }

theorem renamedSame (c: Shape) (x: Nat): setId c x = setIdRenamed c x := rfl

theorem idReadRenamed (c: Shape) (x: Nat): (setIdRenamed c x).id = x := idRead c x

def setIdExtra (c: Shape) (x: Nat) (unused: Nat): Shape := { c | id = x }

theorem extraSame (c: Shape) (x: Nat) (u: Nat): setId c x = setIdExtra c x u := rfl

-- 4. Several dependent fields, two constructors.
type Two =
  | A (n: Nat) (xs: Vec Nat n) (m: Nat) (ys: Vec Nat m)
  | B (n: Nat) (xs: Vec Nat n) (m: Nat) (ys: Vec Nat m)

def replaceBoth (v: Two) (a: Vec Nat (Two.n v)) (b: Vec Nat (Two.m v)): Two :=
  { v | xs = a, ys = b }

test "two dependent fields" :=
  (replaceBoth (B 1 (VCons 1 VNil) 0 VNil) (VCons 5 VNil) VNil).xs == VCons 5 VNil

-- 5. Evidence fields: only the final state has to be valid.
type Range = { start: Nat, stop: Nat, ok: start <= stop }

def widen (r: Range) (a: Nat) (b: Nat) (h: a <= b): Range :=
  { r | start = a, stop = b, ok = h }

type Same = { left: Nat, right: Nat, ok: left = right }

def zero: Same := { left = 0, right = 0, ok = rfl }

def one: Same := { zero | left = 1, right = 1, ok = rfl }

test "evidence" := one.left == 1

type SameVariant =
  | Plain (left: Nat) (right: Nat) (ok: left = right)
  | Tagged (left: Nat) (right: Nat) (ok: left = right) (tag: Nat)

def bump (s: SameVariant): SameVariant := { s | left = 1, right = 1, ok = rfl }

test "evidence in a variant" := (bump (Tagged 0 0 rfl 7)).left == 1

-- 7. A base that is not a variable.
type Pack = { n: Nat, xs: Vec Nat n }

def pick (b: Bool) (r: Pack): Pack := if b then r else r

def replacePicked (b: Bool) (r: Pack) (ys: Vec Nat (pick b r).n): Pack :=
  { pick b r | xs = ys }

test "picked base" :=
  (replacePicked True ({ n = 1, xs = VCons 1 VNil }) (VCons 9 VNil)).xs == VCons 9 VNil

-- 8. Reading back from an updated record computes.
type Point = { x: Nat, y: Nat }

def origin (u: Unit): Point := { x = 0, y = 0 }

theorem readUpdated (p: Point) (a: Nat): ({ p | x = a }).x = a := rfl
theorem readOther (p: Point) (a: Nat): ({ p | x = a }).y = p.y := rfl
theorem readFromCall (u: Unit) (a: Nat): ({ origin u | x = a }).x = a := rfl

-- 9. A variant update keeps the constructor and its own fields.
test "constructor kept" := { Circle 1 2 3 4 | id = 9 } == Circle 1 9 3 4

theorem radiusKept (r: Nat) (i: Nat) (s: Nat) (x: Nat) (q: Nat):
    ({ Circle r i s q | id = x }) = Circle r x s q := rfl

-- Identical inline matches are equal as well.
def sumOptions (xs: List (Option Nat)): Nat :=
  xs.foldLeft (acc o => match o with | Some x => acc + x | None => acc) 0

def sumOptionsAgain (xs: List (Option Nat)): Nat :=
  xs.foldLeft (acc o => match o with | Some x => acc + x | None => acc) 0

theorem inlineMatches (xs: List (Option Nat)): sumOptions xs = sumOptionsAgain xs := rfl

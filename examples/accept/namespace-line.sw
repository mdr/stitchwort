-- The namespace line (docs/proposals/multi-file.md §4.2): this file's
-- declarations go in namespace `Demo`, so the type below is `Demo.Shape`
-- and a hash of it differs from the same type in a file without the line.
namespace Demo

import List (length)

type Point = { x: Nat, y: Nat }

type Shape: Type =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

-- A function on the type, used both ways.
def Shape.area: Shape -> Nat
  | Square s => s * s
  | Rect w h => w * h

-- A namespace of the file's own, and a use of a top-level name written in full.
def Geometry.double (n: Nat): Nat := n + n

def quadruple (n: Nat): Nat := Geometry.double (Demo.double2 n)

def double2 (n: Nat): Nat := n + n

-- A decision procedure, found by `auto`.
type Token: Prop =
  | MkToken

def decToken: Decidable Token := Yes MkToken

def needsToken: [auto t: Token] -> Nat := 1

def main(): {IO} () := IO.print "demo"

test "area" := (Rect 2 3).area == 6 && Shape.area (Square 2) == 4
test "own namespace" := Geometry.double 2 == 4 && quadruple 1 == 4
test "import" := length [1, 2, 3] == 3
test "record" := ({ x = 1, y = 2 }: Point).x == 1
test "auto" := needsToken == 1
test "derived equality" := Rect 1 2 == Rect 1 2 && ({ x = 1, y = 2 }: Point) == { x = 1, y = 2 }

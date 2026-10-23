-- A constructor of a generic type, given number literals, takes the type from
-- its surroundings rather than defaulting the literals to `Nat` first: the
-- expected type (through an alias too), or a sibling operand that already
-- has the type.
import Std (Int, List, Nat, Option)

type Mark (i: Type) (n: Type) =
  | Point (ref: Nat) (label: Text) (at: i)
  | Span (ref: Nat) (label: Text) (from: i) (length: n)

type IntMark = Mark Int Nat

-- The expected type, direct and through an alias.
def direct: Mark Int Nat := Point 1 "p" 10
def aliased: IntMark := Span 2 "s" 10 1000
def listed: List IntMark := [Point 1 "p" 10, Span 2 "s" 10 1000]
def partial: Nat -> IntMark := Span 2 "s" 10
def optional: Option IntMark := Some (Span 2 "s" 10 1000)
def negative: IntMark := Point 1 "p" (-5)

-- No expected type reaches the constructor, but a sibling operand has the
-- type: the constructor is checked after it.
def pair (x: a) (y: a): List a := [x, y]

-- (Nothing expected here: the list's type comes from `m`, not the first item.)
def countList (m: IntMark): Nat := [Point 1 "p" 10, m].length
def countCall (m: IntMark): Nat := (pair (Point 1 "p" 10) m).length
def countIf (m: IntMark) (b: Bool): Nat := (if b then Point 1 "p" 10 else m) |> (_ => 0)

def inList (m: IntMark): List IntMark := [Point 1 "p" 10, m]
def inCall (m: IntMark): List IntMark := pair (Point 1 "p" 10) m
def inIf (m: IntMark) (b: Bool): IntMark := if b then Point 1 "p" 10 else m
def inCompare (m: IntMark): Bool := Point 1 "p" 10 == m
def inCompareBoth (m: IntMark): Bool := Point 1 "p" 10 == m && m == Point 2 "q" 3

def compareCall (n: Nat): IntMark := Point n "p" 10
def inCompareCall: Bool := Point 1 "p" 10 == compareCall 1

-- With nothing else to say, the literal still defaults.
def defaulted: Mark Nat Nat := Point 1 "p" 10

test "the literal is an Int" := inList (Point 3 "q" 4) == [Point 1 "p" 10, Point 3 "q" 4]
test "compared" := inCompareCall

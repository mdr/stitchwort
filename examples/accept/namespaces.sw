-- Namespaces and imports (docs/proposals/namespaces.md, stage 1). The library
-- lives under `Std`. A program sees its core types, their constructors and
-- the operators without asking; everything else is written in full
-- (`List.length`), or imported.

import Text (split, join)
-- `List` here would mean this file's own `List` (below), so the library's
-- is written from `Std`.
import Std.List (reverseOnto)
import Std (Text)

-- A program's own names hide the library's: this file has its own `length`,
-- `Option` and `Yes`.
def length: Nat := 3

type Answer: Type =
  | Yes
  | No

type Option (a: Type): Type =
  | Absent
  | Present (value: a)

-- The library's `Option` is still there, written in full. Its constructors
-- went with the default `Option`, so they're written in full too.
def librarySome: Std.Option Nat := Std.Option.Some 1

-- The program's own `Option` and `Yes`.
def lookup: Nat -> Option Nat
  | 0 => Absent
  | n => Present n

def decide: Nat -> Answer
  | 0 => No
  | n => Yes

test "own names" := length == 3
test "library Option" := Std.List.length [librarySome] == 1
test "own Option" := Std.List.length [lookup 0, lookup 2] == 2

-- A type owns a namespace: its constructors are in it, and so is anything
-- declared with its name in front.
type Shape: Type =
  | Square (side: Nat)
  | Rect (width: Nat) (height: Nat)

def Shape.area: Shape -> Nat
  | Square s => s * s
  | Shape.Rect w h => w * h

test "area" := Shape.area (Rect 2 3) == 6

-- A namespace of the program's own, which no type owns.
def Geometry.double (n: Nat): Nat := n + n

test "own namespace" := Geometry.double (Shape.area (Shape.Square 2)) == 8

-- A file with its own `List` can add to it: `List` means this file's.
type List: Type =
  | Empty
  | More (rest: List)

def List.size: List -> Nat
  | Empty => 0
  | More rest => 1 + List.size rest

test "own List" := List.size (More (More Empty)) == 2

-- Imported names are used without their namespace.
test "imports" := join ',' (split ',' "a,b") == "a,b"
test "imported list function" := Std.List.length (reverseOnto [1, 2] []) == 2

-- `not` is the one function every program sees.
test "not" := not False

-- Operators and literals always mean the library's, whatever names the
-- program declares.
test "operators" := 2 + 2 == 4
test "text operators" := Text.length ("ab" ++ "c") == 3

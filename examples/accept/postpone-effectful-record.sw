-- A record literal with an effectful field (SW-885,
-- docs/proposals/postponement.md): as an argument, a tuple part, a nested
-- field, and where the parameter's type is fixed only by a later argument.
-- The effect pass runs the field first and binds it; the literal left is
-- pure, and waits for its type like any other.
--
-- `Size` has the same fields as `Position`, so the field-name rule can't
-- pick a type for these literals: each one's type comes from where it goes.

import Std (List, Nat, Parse, Result)
import Std.Parse (natDigits)

def shortNumber(): {Parse} Nat := natDigits 1 3

type Position = { x: Nat, y: Nat }

type Size = { x: Nat, y: Nat }

type Robot = { position: Position, speed: Nat }

def usePosition (p: Position): Nat := p.x

-- The parameter's type is known from the signature.
def inArgument(): {Parse} Nat := usePosition { x = shortNumber(), y = 0 }

def inTuple(): {Parse} (Position, Nat) := ({ x = shortNumber(), y = 0 }, 1)

def nested(): {Parse} Robot := { position = { x = shortNumber(), y = 0 }, speed = 0 }

-- The parameter's type is `a`, fixed only by the later argument.
def firstOf (x: a) (xs: List a): a := x

def generic (more: List Position): {Parse} Position := firstOf { x = shortNumber(), y = 0 } more

def area (s: Size): Nat := s.x * s.y

-- The same, for the other record type with these fields.
def sized (more: List Size): {Parse} Nat := area (firstOf { x = shortNumber(), y = 2 } more)

def ok (r: Result Nat Parse.Failure): Nat := match r with
  | Ok n => n
  | Err _ => 999

test "inArgument" := ok (Parse.run ['4', '2'] inArgument) == 42

test "inTuple" := ok (Parse.run ['4', '2'] (() => (inTuple ()).fst.x)) == 42

test "nested" := ok (Parse.run ['7'] (() => (nested ()).position.x)) == 7

test "generic" := ok (Parse.run ['5'] (() => (generic [{ x = 1, y = 1 }]).x)) == 5

test "sized" := ok (Parse.run ['6'] (() => sized [{ x = 1, y = 1 }])) == 12

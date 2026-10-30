-- A copy of ../sw885.sw with run-time tests at the end. Today it is rejected
-- like the original. With the queue prototype of postponement.md §11 on, all
-- its tests pass (30 Oct 2026):
--
--   $ STITCHWORT_QUEUE=1 STITCHWORT_QUEUE_APP=1 STITCHWORT_QUEUE_LIFT=1 \
--       stitchwort test docs/proposals/postponement/prototype/sw885run.sw
--
-- SW-885: a record literal with an effectful field, as an argument, a
-- tuple part or a nested field (SW-883's gaps.sw cases), and `generic`,
-- where the parameter's type is fixed only by a later argument.
--
--   $ stitchwort check docs/proposals/postponement/sw885.sw
--
-- reports E-CANNOT-INFER at the literal in `inArgument`, `inTuple`,
-- `nested` and `generic` (30 Oct 2026).

import Std (List, Nat, Parse, Result)
import Std.Parse (natDigits)

def shortNumber(): {Parse} Nat := natDigits 1 3

type Position = { x: Nat, y: Nat }

-- A second record type with the same fields, so the field-name rule (SW-805,
-- merged after this repro was written) can't pick one: without it the four
-- literals check on main since SW-805.
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

-- Fine today: the whole body, or annotated.
def wholeBody(): {Parse} Position := { x = shortNumber(), y = 0 }

def annotated(): {Parse} Nat := usePosition ({ x = shortNumber(), y = 0 }: Position)

def ok (r: Result Nat Parse.Failure): Nat := match r with
  | Ok n => n
  | Err _ => 999

test "inArgument" := ok (Parse.run ['4', '2'] inArgument) == 42

test "inTuple" := ok (Parse.run ['4', '2'] (() => (inTuple ()).fst.x)) == 42

test "nested" := ok (Parse.run ['7'] (() => (nested ()).position.x)) == 7

test "generic" := ok (Parse.run ['5'] (() => (generic [{ x = 1, y = 1 }]).x)) == 5

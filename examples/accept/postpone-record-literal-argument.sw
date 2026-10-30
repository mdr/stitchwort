-- A record literal whose type only a later argument fixes (SW-817,
-- docs/proposals/postponement.md). `foldLeft`'s accumulator type is unknown
-- when the literal is reached, so the literal waits; `step`, checked after
-- it, says it is a `Tally`, and the literal is then checked as one.
--
-- `Score` has the same fields as `Tally`, so the field-name rule (one record
-- type in scope with exactly these fields) couldn't pick a type here: only
-- `step` does.

import Std (Bool, List, Nat)

type Tally = { enabled: Bool, total: Nat }

type Score = { enabled: Bool, total: Nat }

def step (tally: Tally) (n: Nat): Tally := { enabled = tally.enabled, total = tally.total + n }

def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total

def annotated (ns: List Nat): Nat := (ns.foldLeft ({ enabled = True, total = 0 }: Tally) step).total

def start: Tally := { enabled = True, total = 0 }

def named (ns: List Nat): Nat := (ns.foldLeft start step).total

test "total" := total [1, 2, 3] == 6

test "as annotated" := total [4, 5] == annotated [4, 5] && total [4, 5] == named [4, 5]

test "nothing to add" := total [] == 0

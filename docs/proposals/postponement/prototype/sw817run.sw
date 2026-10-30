-- A copy of ../sw817.sw with run-time tests at the end. Today it is rejected
-- like the original. With the queue prototype of postponement.md §11 on, all
-- its tests pass (30 Oct 2026):
--
--   $ STITCHWORT_QUEUE=1 STITCHWORT_QUEUE_APP=1 STITCHWORT_QUEUE_LIFT=1 \
--       stitchwort test docs/proposals/postponement/prototype/sw817run.sw
--
-- SW-817: an untyped record literal as an argument, whose type only a
-- later argument fixes. `foldLeft`'s accumulator type is unknown when the
-- literal is reached; `step`, checked after it, says it is `Tally`.
--
--   $ stitchwort check docs/proposals/postponement/sw817.sw
--
-- reports E-CANNOT-INFER at the literal in `total` (30 Oct 2026). `annotated`
-- and `named` are what has to be written today.
--
-- `Score` has the same fields as `Tally`, so SW-805's field-name rule (one
-- record type in scope with exactly these fields) doesn't pick a type here
-- either: only `step` can. Without `Score`, SW-805 alone accepts `total`.

import Std (Bool, List, Nat)

type Tally = { enabled: Bool, total: Nat }

type Score = { enabled: Bool, total: Nat }

def step (tally: Tally) (n: Nat): Tally := { enabled = tally.enabled, total = tally.total + n }

def total (ns: List Nat): Nat := (ns.foldLeft { enabled = True, total = 0 } step).total

def annotated (ns: List Nat): Nat := (ns.foldLeft ({ enabled = True, total = 0 }: Tally) step).total

def start: Tally := { enabled = True, total = 0 }

def named (ns: List Nat): Nat := (ns.foldLeft start step).total

test "total" := total [1, 2, 3] == annotated [1, 2, 3] && total [1, 2, 3] == 6

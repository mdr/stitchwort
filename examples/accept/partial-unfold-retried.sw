-- metrics: match-retried: without-partial-unfold
-- metrics: rewrite-retried: without-partial-unfold
-- A `match` that kept the partial unfold is made again without it if the
-- whole `match` then fails, and so is a `rewrite … at h` used as a term.
-- `glue && False` is found by opening only `step`, so the `False` arm's
-- goal keeps `S.past` folded, and `stale c bs` then fails its round trip
-- inside it (E-REWRITE-MOTIVE). The arm's `rewrite` used no partial
-- unfold of its own, so only the `match` around it can undo the step: made
-- again with the step off, it hands its arms the goal as before the step
-- existed, and both rules apply. In `atAny`, `Bool.andFalse glue` opens
-- `step` in `h`'s type in the same way. (SW-4444, after SW-4419's
-- examples/accept/rewrite-partial-unfold-retried.sw;
-- docs/proposals/partial-unfold.md §3.)
import Std (Bool)

def sb (fresh: Bool) (c: Nat) (bs: List Nat): List Nat := match bs with
  | [_, ..o] => if fresh then [c, ..o] else bs
  | [] => []

def stp (fresh: Bool) (c: Nat) (bs: List Nat) (top: Nat): Nat := if fresh && bs.isEmpty then c else top

type S = { bs: List Nat, top: Nat, start: Bool, glue: Bool }

def S.past (s: S) (c: Nat) (fresh glue: Bool): S :=
  { bs = sb fresh c s.bs, top = stp fresh c s.bs s.top, start = False, glue }

def S.step (s: S) (c k: Nat) (ls: Bool): Option S :=
  if s.glue && ls then None
  else if k == 0 then Some { s | start = True }
  else Some (s.past c (s.start && ls) (k == 1))

theorem stale ∀ (c: Nat) (bs: List Nat): sb False c bs = bs := match bs with | [] | [_, .._] => byComputing

theorem stepAny ∀ (s: S) (c d k: Nat): s.step c k False = s.step d k False := match s with
  | { bs, top, start, glue } =>
    match glue && False with
      | True => byComputing
      | False => rewrite Bool.andFalse start, stale c bs

theorem atAny ∀ (bs: List Nat) (top: Nat) (start glue: Bool) (c d k: Nat)
    (h: S.step { bs, top, start, glue } c k False = S.step { bs, top, start, glue } d k False):
    True :=
  let h2 := rewrite Bool.andFalse glue, Bool.andFalse start, stale c bs at h
  byComputing

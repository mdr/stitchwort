-- metrics: rewrite-retried: without-partial-unfold
-- A `rewrite` whose first rule took the partial unfold is made again
-- without it if the whole `rewrite` then fails. `Bool.andFalse glue` finds
-- `glue && False` by opening only `step`, so the goal keeps `s.past c False
-- …` folded. The third rule's `sb False c bs` is then inside `past`, and
-- replacing it there doesn't survive the round trip through the partly
-- folded goal. Made again over the computed goal, as before the step
-- existed, all three rules apply. (SW-4419; reduced from `tools/fmt`'s
-- `PrintHangProofs.stepColumn`. docs/proposals/partial-unfold.md §3.)
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
  | { bs, top, start, glue } => rewrite Bool.andFalse glue, Bool.andFalse start, stale c bs

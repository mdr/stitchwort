-- `rewrite` (on the goal, and `at h`) looks for its left side in the goal as
-- the goal shows it first, calls kept, and solves the rule's unknowns by the
-- arguments of a call. Only when that finds nothing, or leaves a copy hidden
-- inside a call, does it search what the goal computes to, as before.
-- (docs/syntax.md, "rewrite"; docs/proposals/goal-as-written.md.)
import Std (Bool, Eq, List, Nat, Or)

type Report = { levels: List Nat }

def Report.isSafe (report: Report): Bool := report.levels.all (n => n < 10)

def safe (report: Report): Bool := report.levels.all (n => n < 20)

-- `Report.isSafe ?0` computes to `List.all ?0.levels …`, which cannot be
-- matched against `List.all (List.reverse xs) …` to find `?0`; as written,
-- the call's argument solves it.
theorem unknownSolved ∀ (isSafeCorrect: ∀ (report: Report) => report.isSafe = safe report) (xs: List Nat):
    Report.isSafe { levels = xs.reverse } = safe { levels = xs.reverse } :=
  rewrite isSafeCorrect _

type Image = { rows: List Nat }

def Image.flip (image: Image): Image := { rows = image.rows.reverse }

def edges (image: Image): List Nat := [image.rows.headOr 0, image.rows.length]

-- `edge ∈ edges image.flip` computes to a disjunction, but the left side of
-- the rule is there as written.
theorem inHypothesis ∀ (image: Image) (a: Nat) (b: Nat) (flipEdges: edges image.flip = [a, b])
    (edge: Nat) (member: edge ∈ edges image.flip): edge ∈ [a, b] :=
  rewrite flipEdges at member in member

-- The only occurrence is inside the call `safe …`, which the goal shows as
-- a call: found in what it computes to, as before.
theorem insideACall ∀ (xs: List Nat) (h: xs.all (n => n < 20) = True): safe { levels = xs } = True :=
  rewrite h

-- One occurrence shown, one inside a call: all of them are rewritten.
theorem shownAndHidden ∀ (xs: List Nat) (h: xs.all (n => n < 20) = True):
    xs.all (n => n < 20) = safe { levels = xs } :=
  rewrite h

-- `per` carries a proof that the divisor is not zero, which a goal as
-- written would have to rewrite too (its type is `d ≠ 0`, not `x' ≠ 0`), so
-- the search falls back to the computed goal, where the proof is gone. (The
-- shape of aoc 2025 day 1, Part2.sw, when its `/` took a proof: a step in a
-- `calc`.)
def per (n: Nat) (d: Nat) [auto ok: d ≠ 0]: Nat := n / d

theorem hiddenProof ∀ (d: Nat) [auto ok: d ≠ 0] (a: Nat) (n: Nat) (same: Succ a = d):
    per (d + n) d = per (Succ a + n) d :=
  calc per (d + n) d
    _ = per (Succ a + n) d := rewrite (omega: d = Succ a)

theorem hiddenProofPlain ∀ (d: Nat) (a: Nat) (n: Nat) [auto ok: d ≠ 0] (same: d = Succ a):
    per (d + n) d = per (Succ a + n) d :=
  rewrite same

def add (x: Nat) (y: Nat): Nat := match y with
  | Zero => x
  | Succ k => Succ (add x k)

def wrap (n: Nat) (k: Nat): Nat := add k n

-- With unknowns, the instance is the one the search over the computed goal
-- would pick, `add c (add a b)` (first in that goal), not the `add a b`
-- the goal shows; the as-written result is dropped for that reason.
theorem sameInstance ∀ (comm: ∀ (x y: Nat) => add x y = add y x) (a: Nat) (b: Nat) (c: Nat):
    wrap (add a b) c = add (add a b) c :=
  rewrite comm _ _ in rfl

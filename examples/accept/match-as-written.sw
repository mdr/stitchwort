-- expect-warning: W-MATCH-NOT-FOUND
-- A generalised `match` (and `cases`) looks for its expression in the goal
-- as the goal shows it first, calls kept, comparing up to computation, so
-- an expression written differently from the goal is found and the arms
-- keep the goal's calls. Only if that finds what the search over the
-- computed goal finds (and perhaps more written differently) is it used;
-- otherwise the `match` refines what it did before. (docs/syntax.md,
-- "Generalised `match`"; docs/proposals/goal-as-written.md, stage 2.)
import Std (Bool, Eq, List, Nat, Option, Or)

def chain (fuel: Nat) (lists: List (List Nat)): Nat := match fuel with
  | Zero => 0
  | Succ more => lists.map (chainThrough more) |> .maximum |> .getOrElse 0

def chainThrough (fuel: Nat): (xs: List Nat) → Nat
  | [] => 0
  | [only] => chain fuel [] + 1
  | [first, ..rest] => 0

-- The goal has `xs => chainThrough more xs` (the recursive call was
-- elaborated so), the scrutinee `chainThrough more`: the same up to eta.
-- `each`'s type has the scrutinee exactly as written. (AoC 2020 day 19,
-- `chainBounded`.)
theorem upToEta ∀ (more: Nat) (lists: List (List Nat)) (cap: Nat)
    (each: ∀ (most: Nat) => lists.map (chainThrough more) |> .maximum = Some most → most ≤ cap):
    chain (Succ more) lists ≤ cap :=
  match found: lists.map (chainThrough more) |> .maximum with
    | None => omega
    | Some most => omega [each most found]

def isBig (n: Nat): Bool := 10 < n

def label (n: Nat): Nat := if isBig n then 1 else 0

-- `isBig n` is shown on the left and hidden inside `label n` on the right:
-- the search over the computed goal refines both, as before.
theorem hiddenInACall ∀ (n: Nat): (if isBig n then 1 else 0) = label n := match big: isBig n with
  | True => rfl
  | False => rfl

def pick (b: Bool): Nat := if b then 1 else 0

-- `isBig 20` computes to `True`, so the computed goal is `1 = 1` and has no
-- occurrence; refining the call as written would make the `False` arm
-- `pick False = 1`. The `match` refines nothing, as before.
theorem computedAway: pick (isBig 20) = 1 := match big: isBig 20 with
  | True => rfl
  | False => rfl

def double (n: Nat): Nat := n + n

-- The arms keep the goal's calls: the `True` arm's goal is `double a =
-- double a` (where it was `a + a = a + a`), and a lemma about `double`
-- finds it as written.
theorem armsKeepCalls ∀
    (doubled: ∀ (n: Nat) => double n = 2 * n)
    (flag: Bool) (a: Nat):
    (if flag then double a else 0) = (if flag then 0 + double a else 0) :=
  match e: flag with
    | True => rewrite doubled a in rfl
    | False => rfl

def Ignore (a: Type) (b: Bool): Type := a

-- `k`'s type mentions `isBig n` only as written (it computes to `Nat`), so
-- the search over the computed goal doesn't copy `k`, and neither does the
-- one as written: a copy would forget that `k` is 5.
theorem letKept ∀ (n: Nat): pick (isBig n) ≤ 1 :=
  let k: Ignore Nat (isBig n) := 5
  match e: isBig n with
    | True => (let same: k = 5 := rfl; omega)
    | False => (let same: k = 5 := rfl; omega)

def bump (n: Nat): Nat :=
  let k: Ignore Nat (isBig n) := 5
  match e: isBig n with
    | True => k
    | False => k + 1

theorem bumpValue: bump 20 = 5 := rfl

def keep (a: Nat) (b: Bool): Nat := a

-- `isBig n` is shown, but `keep` drops it, so nothing the arms see would
-- change: not found, and the warning says so.
theorem vanishing ∀ (n: Nat): keep 3 (isBig n) = 3 := match e: isBig n with
  | True => rfl
  | False => rfl

-- expect-warning: W-MATCH-UNCONFIRMED
-- expect-warning: W-REWRITE-UNCONFIRMED
-- When the goal (or a hypothesis) is too large to compute in full, the
-- usual search for a `rewrite`'s left side or a `match`'s expression,
-- which looks at what the goal computes to, can't run. If the term is
-- found as the goal shows it, that is used, with a warning that copies
-- hidden inside calls weren't looked for. (docs/syntax.md, "rewrite" and
-- "Generalised `match`"; docs/proposals/goal-as-written.md, stage 4.)
import Std (Bool, Eq, Nat, Option, Void)

def step (n: Nat) (k: Nat): Nat := n * k + 1

-- Each round is an `if` stuck on `x`, so `settle x k 3000` computes to
-- three thousand nested `if`s, too large to show.
def settle (x: Nat) (k: Nat): (rounds: Nat) → Option Nat
  | Zero => None
  | Succ more =>
    let next := step x k
    if next == x then Some x else settle next k more

def limit: Nat := 3000

-- `solved`'s type holds `settle x k limit` as written. (The shape of AoC
-- 2020 day 11, `settledExactly`, with the limit written as `roundLimit`.)
theorem matchAtLimit ∀ (x: Nat) (k: Nat) (answer: Nat)
    (solved: (settle x k limit |> .map (n => n + 1)) = Some answer): ∃ (y: Nat) => answer = y + 1 :=
  match found: settle x k limit with
    | None => Void.exfalso (Option.noneNotSome answer solved)
    | Some y => Witness y (Eq.sym (Option.someInjective solved))

theorem rewriteAtLimit ∀ (x: Nat) (k: Nat) (y: Nat) (settles: settle x k limit = Some y)
    (q: Option Nat → Prop) (h: q (Some y)): q (settle x k limit) :=
  rewrite settles in h

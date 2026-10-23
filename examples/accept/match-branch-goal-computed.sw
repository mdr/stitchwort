-- SW-206 (3): a `match` branch's goal has already computed one step
-- (`twice (Succ k)` is `Succ (Succ (twice k))` there), so a proof is written for
-- that goal. A lemma stated for the folded form still fits, because types are
-- compared up to computing; only what looks for a shape (`rewrite` of a hidden
-- `match`'s part, a lemma about the call of a generated `match`) needs the
-- computed form (docs/syntax.md, "Nothing else changes").
import Std (Nat, Eq)

def twice: Nat -> Nat
  | Zero => 0
  | Succ n => Succ (Succ (twice n))

theorem twiceSucc (k: Nat): twice (Succ k) = Succ (Succ (twice k)) := rfl

-- The goal in the second branch is `Succ (Succ (twice k)) = Succ (k + Succ k)`,
-- which the lemma's statement equals by computing.
theorem twiceAdd (n: Nat): twice n = n + n :=
  match n with
    | Zero => rfl
    | Succ k => Eq.trans (twiceSucc k) (omega [twiceAdd k])

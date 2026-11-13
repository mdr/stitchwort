-- A branch equation takes its condition's proof as a hypothesis, and a
-- branch may use that proof, here in `%`'s `auto` proof that `n ≠ 0`. The
-- definition's own proof and the hypothesis are two proofs of one
-- proposition, which the kernel doesn't tell apart (docs/core.md, proofs are
-- inert), so the equation holds by computation whatever the proposition is.

def remainder: (Nat, Nat) → Nat
  | (n, len) if n != 0 => len % n
  | _ => 0

theorem usesProof ∀ (n len: Nat) (positive: n ≠ 0): remainder (n, len) = len % n := remainder.eq1 n len positive

def remainderOf (n len: Nat): Nat := if h: n ≠ 0 then len % n else 0

theorem remainderOfPositive ∀ (n len: Nat) (positive: n ≠ 0): remainderOf n len = len % n :=
  remainderOf.eq.ifTrue n len positive

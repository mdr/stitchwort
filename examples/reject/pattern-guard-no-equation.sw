-- expect-error: E-NO-EQUATION
-- A guarded arm has an equation taking its condition as a hypothesis, but
-- not where its right side uses the condition's proof (here `%`'s
-- `auto` proof that `n ≠ 0`): two proofs of `n ≠ 0` aren't known to be
-- equal without proof irrelevance (D2180).

def remainder: (Nat, Nat) → Nat
  | (n, len) if n != 0 => len % n
  | _ => 0

theorem usesProof (n len: Nat) (positive: n ≠ 0): remainder (n, len) = len % n := remainder.eq1 n len positive

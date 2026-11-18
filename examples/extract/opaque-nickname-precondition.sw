-- An export whose precondition only shows through an opaque nickname it
-- unfolds: the generated wrapper still checks it at runtime (SW-3936).
--
-- run: share 10 2
-- rejects: share 10 0

opaque def Split: Type := (total people: Nat) → [auto ok: people ≠ 0] → Nat

export opaque def share: Split unfolding Split := total people => total / people

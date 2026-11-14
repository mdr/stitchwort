-- An export with a precondition. JS can't pass a proof that `percent <= 100`,
-- so the generated wrapper checks it at runtime (with the same decision
-- procedure `auto` would use), and refuses inputs that fail it.
--
-- (Small numbers: `Nat` is unary inside the compiler for now.)
--
-- run: applyDiscount 8 25
-- run: applyDiscount 4 100
-- run: applyDiscount 6 0
-- rejects: applyDiscount 5 150
-- run: perPerson 10 3
-- rejects: perPerson 10 0
-- rejects: perPerson 2 0

export def applyDiscount (price percent: Nat): [auto ok: percent ≤ 100] → Nat := price - price * percent / 100

-- The precondition refuses a split between no people, where `/` would give 0.
export def perPerson (total people: Nat): [auto ok: people ≠ 0] → Nat := total / people

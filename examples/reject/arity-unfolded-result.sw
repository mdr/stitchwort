-- expect-error: E-ARITY
-- The result `Holds n` unfolds to a function type, so arms match its
-- argument too; the note names `Holds` and the argument `m` it adds.
def Holds (n: Nat): Prop := (m: Nat) → n + m = m + n

theorem holdsAll: (n: Nat) → Holds n
  | n => Nat.addComm n

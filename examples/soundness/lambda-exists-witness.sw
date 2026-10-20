-- expect-error: E-PROP-ELIM
-- The same through a lambda's pattern parameter.
type Exists (p: Nat -> Prop): Prop =
  | Witness (x: Nat) (proof: p x)

def witness (p: Nat -> Prop): Exists p -> Nat := (Witness x h) => x

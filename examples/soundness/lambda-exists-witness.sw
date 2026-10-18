-- expect-error: E-PROP-ELIM
-- The same through a lambda's pattern parameter.
type Exists (p : Nat -> Prop) : Prop =
  | Witness (x : Nat) (proof : p x)

witness : (p : Nat -> Prop) -> Exists p -> Nat
witness p = \(Witness x h) -> x

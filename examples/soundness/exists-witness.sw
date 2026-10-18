-- expect-error: E-PROP-ELIM
-- The witness of an existence proof is erased, so it can't be returned as data.
type Exists (p : Nat -> Prop) : Prop =
  | Witness (x : Nat) (proof : p x)

def witness (p : Nat -> Prop) : Exists p -> Nat
  | Witness x h => x

-- expect-error: E-PROP-ELIM
-- The pattern covers every constructor of a proposition but would extract
-- data (the erased witness) from a proof.
type Exists (p : Nat -> Prop) : Prop =
  | Witness (x : Nat) (proof : p x)

witness : (p : Nat -> Prop) -> Exists p -> Nat
witness p e =
  let Witness x h = e
  x

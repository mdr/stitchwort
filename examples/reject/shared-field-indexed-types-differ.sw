-- expect-error: E-UNKNOWN-FIELD
-- In an indexed family the field's type must be the same in every
-- constructor: `value` is `Nat` in `N` but `Bool` in `B`.

type Box: Type -> Type 1 =
  | N (value: Nat): Box Nat
  | B (value: Bool): Box Bool

def bv (b: Box Nat): Nat := b.value

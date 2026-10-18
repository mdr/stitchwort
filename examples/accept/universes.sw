-- Pairs with soundness/type-in-type.sw and soundness/large-field.sw.
def typeInType1 : Type 1 := Type

type Box : Type 1 =
  | MkBox (t : Type)

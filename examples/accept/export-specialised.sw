-- Pairs with reject/export-polymorphic.sw: a version specialised to `Nat`.
identity : a -> a
identity x = x

export
identityNat : Nat -> Nat
identityNat n = identity n

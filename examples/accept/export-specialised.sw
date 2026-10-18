-- Pairs with reject/export-polymorphic.sw: a version specialised to `Nat`.
def identity (x : a) : a := x

export def identityNat (n : Nat) : Nat := identity n

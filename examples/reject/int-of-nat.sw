-- expect-error: E-UNKNOWN-NAME
-- `Int.ofNat` isn't a name: a `Nat` becomes an `Int` with `Nat.toInt`.
-- The suggestion reads the conversion the other way round.
def x: Int := Int.ofNat 3

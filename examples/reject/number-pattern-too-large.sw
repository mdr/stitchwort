-- expect-error: E-UNSUPPORTED
-- A number pattern becomes that many nested `Succ` patterns, so they're
-- limited. Compare with `==` instead.
isBig : Nat -> Bool
isBig 1000 = True
isBig n    = False

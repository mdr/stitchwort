-- expect-error: E-TYPE-MISMATCH
-- `|>` puts the value first, as dot notation does (D303): `m |> Meter.scale 2`
-- is `Meter.scale m 2`, so `m` lands where the factor goes.

type Meter = { v: Nat }

def Meter.scale (k: Nat) (m: Meter): Meter := { v = k * m.v }

def doubled (m: Meter): Meter := m |> Meter.scale 2

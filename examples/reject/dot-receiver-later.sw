-- expect-error: E-DOT-NO-RECEIVER
-- Dot notation puts the value first (D303): `m.scale 2` is `Meter.scale m 2`,
-- but `Meter.scale` takes the factor first. It doesn't look for a later
-- `Meter` parameter; the definition also warns (W-RECEIVER-NOT-FIRST).

type Meter = { v: Nat }

def Meter.scale (k: Nat) (m: Meter): Meter := { v = k * m.v }

def doubled (m: Meter): Meter := m.scale 2

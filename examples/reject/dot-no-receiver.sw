-- expect-error: E-DOT-NO-RECEIVER
-- `m.parse` finds `Meter.parse`, which has no `Meter` parameter to put `m`
-- in. Lookup stops there: it doesn't go on to look elsewhere.

type Meter = { v : Nat }

def Meter.parse (t : Text) : Meter := { v = Text.length t }

def again (m : Meter) : Meter := m.parse

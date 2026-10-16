-- expect-error: E-DOT-NO-RECEIVER
-- `m.parse` finds `Meter.parse`, which has no `Meter` parameter to put `m`
-- in. Lookup stops there: it doesn't go on to look elsewhere.

type Meter = { v : Nat }

Meter.parse : Text -> Meter
Meter.parse t = { v = Text.length t }

again : Meter -> Meter
again m = m.parse

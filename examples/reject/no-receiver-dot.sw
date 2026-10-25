-- expect-error: E-DOT-NO-RECEIVER
-- `@[noReceiver]` only silences the definition's warning: dot notation still
-- puts the value first, and `Meter.add` takes a `Nat` there.

type Meter = { v: Nat }

@[noReceiver]
def Meter.add (n: Nat) (m: Meter): Meter := { v = n + m.v }

def more (m: Meter): Meter := m.add 1

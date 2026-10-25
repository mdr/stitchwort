-- expect-error: E-ATTRIBUTE
-- `@[noReceiver]` is for plain definitions: a theorem gets no
-- W-RECEIVER-NOT-FIRST warning to silence.

type Meter = { v: Nat }

@[noReceiver]
theorem Meter.same (n: Nat) (m: Meter): m = m := rfl

-- expect-error: E-NOT-A-TYPE
-- `if h:` takes a proposition, and a `Bool` isn't one. The note says to
-- write `if b then`, or `if h: b = True then` to keep the proof (SW-1015).

theorem choose (b: Bool): Or (b = True) (Not (b = True)) := if h: b then Inl h else Inr h

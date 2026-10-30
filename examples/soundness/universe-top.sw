-- expect-error: E-UNIVERSE
-- `Type 65535` is the largest universe, so nothing holds it and it can't be
-- used as a term, here a type annotation (SW-902). `Type 65535 : Type 65535`
-- would be as unsound as `Type : Type`.
def top: Type 65535 := Type 65534

-- expect-error: E-UNIVERSE
-- `Type : Type` would allow paradoxes (Girard's) that break both proofs and
-- termination.
def typeInType : Type := Type

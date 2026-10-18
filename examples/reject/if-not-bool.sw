-- expect-error: E-TYPE-MISMATCH
-- A condition that's neither a `Bool` nor a proposition: the `Bool` reading's
-- error is reported.
def pick (t : Text) : Nat := if t then 1 else 2

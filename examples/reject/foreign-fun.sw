-- expect-error: E-TYPE-MISMATCH
-- Lean's `fun x => e` is written `x => e`: `fun` is read as the lambda's
-- first parameter, so the lambda has two parameters instead of one.
def inc: Nat -> Nat := fun x => x + 1

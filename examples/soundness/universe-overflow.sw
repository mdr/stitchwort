-- expect-error: E-PARSE
-- SW-902: `Type 4294967295 : Type 0` once held, since the step to the next
-- universe wrapped at `u32::MAX`: a cyclic hierarchy, as in Girard's paradox.
-- Levels now stop at `Type 65535`. Pairs with accept/universe-limit.sw.
def wrap: Type 0 := Type 4294967295

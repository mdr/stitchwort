-- A lambda whose first parameter hides a zero-argument function doesn't warn:
-- `entry m => …` can't have been meant as `entry (m => …)`, since `entry`
-- takes no explicit arguments. (It is still a lambda with two parameters, as
-- the types show.)
def entry (): Nat := 1

def shadowed: Nat → Nat → Nat := entry m => m

test "the lambda is the function written" := shadowed 1 3 == 3

-- expect-error: E-TERMINATION
-- Swapping the arguments with nothing getting smaller: two calls in a row
-- give back the same arguments. (Compare `interleave` in
-- accept/size-change.sw, which also takes a part of one of them.)
def swap (x: Nat) (y: Nat): Nat := swap y x

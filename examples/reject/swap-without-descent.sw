-- expect-error: E-TERMINATION
-- Swapping the arguments with nothing getting smaller: two calls in a row
-- give back the same arguments. (Compare `interleave` in
-- accept/size-change.sw, which also takes a part of one of them.)
swap : Nat -> Nat -> Nat
swap x y = swap y x

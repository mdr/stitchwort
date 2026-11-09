-- expect-error: E-TYPE-MISMATCH
-- The mismatch note unfolds `n + 2^128` one `Succ` at a time, up to the
-- size limit, and frees the result: millions of calls nested in each
-- other's unfoldings, which once overflowed the stack (SW-2452).
import Std (List, Nat)

def inside (x n: Nat): Bool := x in 1 ..= n

theorem insideIff (x n: Nat): (inside x n = True) ↔ (x ∈ 2 ..= n) :=
  List.inRangeIff x 1 (n + 340282366920938463463374607431768211456)

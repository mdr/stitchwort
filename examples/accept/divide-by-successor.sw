-- A divisor `n + k`, with `k` a literal above 0, is never 0, so `auto`
-- proves `n + 1 ≠ 0` without a test, as it does `Succ n ≠ 0`: `+` computes on
-- its second argument too, so `n + 1` is `Succ n` (games/rogue/NOTES.md §2;
-- accept/plus-both-sides.sw).
-- `n + m`, with both unknown, still needs a test (reject/divide-by-unknown.sw).

-- A roll from 0 up to `most`.
def upTo (seed: Nat) (most: Nat): Nat := seed % (most + 1)

def perPair (total: Nat) (pairs: Nat): Nat := total / (pairs + 2)

-- The same as `Succ most`, which was always accepted.
def upToSucc (seed: Nat) (most: Nat): Nat := seed % Succ most

test "upTo" := upTo 10 2 == 1 && upTo 7 0 == 0 && upTo 6 6 == 6

test "perPair" := perPair 10 3 == 2

test "the same as Succ" := upTo 1234 9 == upToSucc 1234 9

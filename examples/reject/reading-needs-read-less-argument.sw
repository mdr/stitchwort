-- expect-error: E-TYPE-MISMATCH
-- An `e = False` fact isn't its reading: `h` is `(m <= n) = False`, and the
-- note says it reads as `n < m` and that `.read` gives that
-- (docs/proposals/bool-as-proposition.md §6.7). The lemma's implicit type
-- parameter is still unknown when the argument is checked.
import Std (Nat, Ord)

def earlier [auto ord: Ord a] (m n: a) (h: n < m): Nat := 0

def call (m n: Nat) (h: (m <= n) = False): Nat := earlier m n h

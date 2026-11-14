-- expect-error: E-TYPE-MISMATCH
-- An `e = False` fact isn't its reading: `same` is `(a == b) = False`, and the
-- note says it reads as `a ≠ b` and that `.read` gives that
-- (docs/proposals/bool-as-proposition.md §6.7). The lemma's implicit type
-- parameter is still unknown when the argument is checked.
import Std (Nat, Ord)

def apart [auto ord: Ord k] (a b: k) (h: a ≠ b): Nat := 0

def call [auto ord: Ord k] (a b: k) (same: (a == b) = False): Nat := apart a b same

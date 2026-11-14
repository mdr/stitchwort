-- expect-error: E-TYPE-MISMATCH
-- An `e = False` fact isn't its reading: the theorem's body is `same`, of type
-- `(a == b) = False`, where `a ≠ b` is wanted, and the note says `.read` gives
-- that (docs/proposals/bool-as-proposition.md §6.7).
import Std (Nat)

theorem apart (a b: Nat) (same: (a == b) = False): a ≠ b := same

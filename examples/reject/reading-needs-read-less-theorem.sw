-- expect-error: E-TYPE-MISMATCH
-- An `e = False` fact isn't its reading: the theorem's body is `h`, of type
-- `(m <= n) = False`, where `n < m` is wanted, and the note says `.read`
-- gives that (docs/proposals/bool-as-proposition.md §6.7).
import Std (Nat)

theorem earlier (m n: Nat) (h: (m <= n) = False): n < m := h

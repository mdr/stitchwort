-- expect-error: E-TYPE-MISMATCH
-- `match some` gives `Some` of each result, so what it makes is an `Option`;
-- here a `Nat` is expected.
import Std (Nat)

type Scan =
  | Corrupted (illegal: Nat)
  | Fine

def illegal: Scan → Nat := match some | Corrupted n => n

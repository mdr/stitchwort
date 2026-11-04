-- expect-error: E-TYPE-MISMATCH
-- `matches` gives a `Bool` (`True` where an arm matches, `False` for the
-- rest), so it can't be used where a `Nat` is expected.
import Std (Nat)

type Scan =
  | Corrupted (illegal: Nat)
  | Fine

def illegal: Scan → Nat := matches | Corrupted _

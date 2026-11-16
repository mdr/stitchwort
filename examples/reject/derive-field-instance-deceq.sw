-- expect-error: E-TYPE-MISMATCH
-- `Thing`'s derived `DecEq` waits for the failed `colorDecEq`, so `==` on
-- it waits too, rather than reporting a second error (SW-3078).
import Std (DecEq)

type Color =
  | Red
  | Green

instance colorDecEq: DecEq Color := True

type Thing = { color: Color }

def red: Thing := { color = Red }

test "same" := red == red

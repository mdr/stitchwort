-- expect-error: E-TYPE-MISMATCH
-- `Thing`'s derived `Show` waits for the failed `colorShow`, so showing one
-- waits too, rather than reporting a second error (SW-3078).
import Std (Show)

type Color =
  | Red
  | Green

instance colorShow: Show Color := True

type Thing = { color: Color }

def red: Thing := { color = Red }

test "shown" := "${red}" == "{ color = Red }"

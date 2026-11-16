-- expect-error: E-TYPE-MISMATCH
-- `Thing`'s derived `Finite` waits for the failed `colorFinite`, so listing
-- every `Thing` waits too, rather than reporting a second error (SW-3078).
import Std (Finite, List)

type Color =
  | Red
  | Green

instance colorFinite: Finite Color := True

type Thing = { color: Color }

def things: List Thing := Finite.all

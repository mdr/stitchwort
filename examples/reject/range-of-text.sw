-- expect-error: E-TYPE-MISMATCH
-- Ranges are of numbers; `Nat` for now.
import Std (List, Nat, Text)

def letters: List Nat := "a" ..< "z"

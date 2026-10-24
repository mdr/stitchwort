-- expect-error: E-SAFE-LITERAL
-- A numeral is a `SafeNat` or `SafeInt` only within 2^53 - 1 of zero (SW-354).
import Std (List, SafeInt, SafeNat)

def tooLarge: SafeNat := 9007199254740992

def tooSmall: List SafeInt := [1, -9007199254740992]

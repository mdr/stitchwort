-- expect-error: E-TYPE-MISMATCH
-- `Float` and `Int` don't mix, with or without a minus sign.
import Std (Float)

def plus (t: Float) (i: Int): Float := t + i

def plusNegated (t: Float) (i: Int): Float := t + (-i)

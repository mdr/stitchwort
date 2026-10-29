-- Where `cases` stops: every variable matters on both sides, so 2^n cases.
-- Six `Bool`s (64 cases) check; seven give E-CASES-BUDGET:
--   theorem xor7 (a b c d e f g: Bool): … := cases
--   [E-CASES-BUDGET] Error: `cases` made more than 64 cases without closing them all
--     Note 1: it split on 7: `a`, `b`, `c`, `d`, `e`, `f`, `g`
--     Note 2: the first case still open: a = True, b = False, c = False, d = False, e = False
import Std (Bool)

def xor (a: Bool) (b: Bool): Bool := if a then not b else b

theorem xor6 (a: Bool) (b: Bool) (c: Bool) (d: Bool) (e: Bool) (f: Bool):
    xor a (xor b (xor c (xor d (xor e f)))) = xor f (xor e (xor d (xor c (xor b a)))) := cases

-- expect-error: E-CASES-BUDGET
-- Seven `Bool`s are 128 cases, more than `cases` makes (64).
import Std (Bool)

theorem xorReverse (a: Bool) (b: Bool) (c: Bool) (d: Bool) (e: Bool) (f: Bool) (g: Bool):
    Bool.xor a (Bool.xor b (Bool.xor c (Bool.xor d (Bool.xor e (Bool.xor f g)))))
      = Bool.xor g (Bool.xor f (Bool.xor e (Bool.xor d (Bool.xor c (Bool.xor b a))))) := cases

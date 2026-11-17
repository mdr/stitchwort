-- expect-error: E-CASES-BUDGET
-- Nine `Bool`s are 512 cases, more than `cases` makes (64, and 256 on its
-- second try).
import Std (Bool)

theorem xorReverse ∀ (a b c d e f g h i: Bool):
    Bool.xor a (Bool.xor b (Bool.xor c (Bool.xor d (Bool.xor e (Bool.xor f (Bool.xor g (Bool.xor h i)))))))
      = Bool.xor i (Bool.xor h (Bool.xor g (Bool.xor f (Bool.xor e (Bool.xor d (Bool.xor c (Bool.xor b a))))))) :=
  cases

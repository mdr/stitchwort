-- expect-error: E-CASES-BUDGET
-- `Int.natAbs` tests its `Int`'s constructors, so `cases` takes the `Int`s
-- apart: nine of them are 512 cases, more than `cases` makes (64, and 256
-- on its second try).
import Std (Int)

theorem absProductReverse ∀ (a b c d e f g h i: Int):
    Int.natAbs a
      * Int.natAbs b
      * Int.natAbs c
      * Int.natAbs d
      * Int.natAbs e
      * Int.natAbs f
      * Int.natAbs g
      * Int.natAbs h
      * Int.natAbs i
      = Int.natAbs i
        * Int.natAbs h
        * Int.natAbs g
        * Int.natAbs f
        * Int.natAbs e
        * Int.natAbs d
        * Int.natAbs c
        * Int.natAbs b
        * Int.natAbs a :=
  cases

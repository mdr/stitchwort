-- expect-error: E-CASES-BUDGET
-- `Int.natAbs` tests its `Int`'s constructors, so `cases` takes the `Int`s
-- apart: seven of them are 128 cases, more than `cases` makes (64).
import Std (Int)

theorem absReverse (a: Int) (b: Int) (c: Int) (d: Int) (e: Int) (f: Int) (g: Int):
    Int.natAbs a + Int.natAbs b + Int.natAbs c + Int.natAbs d + Int.natAbs e + Int.natAbs f + Int.natAbs g
      = Int.natAbs g + Int.natAbs f + Int.natAbs e + Int.natAbs d + Int.natAbs c + Int.natAbs b + Int.natAbs a := cases

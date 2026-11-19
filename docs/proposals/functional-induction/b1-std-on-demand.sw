-- Expected to fail today (E-NO-INDUCT, "doesn't call itself"): finding B1, std's f.induct not made for `match induct` alone.
import Std (Bool, Char, Eq, List, Nat, Text)
theorem t ∀ (p: Char → Bool) (xs: List Char): List.dropWhile xs p = List.dropWhile xs p := match induct (List.dropWhile
    xs p) with
  | eq1 => byComputing

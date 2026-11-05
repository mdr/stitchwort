-- expect-error: E-OMEGA
-- The two atoms apply `List.length` to `List.take` calls that differ only in
-- their count; no fact connects them, so `omega` can't relate them.
import Std (List, Nat)

theorem lengthBounds (xs: List Nat) (count: Nat) (length: Nat)
    (h: List.length (List.take xs count) ≤ 3):
    List.length (List.take xs length) ≤ 3 := omega

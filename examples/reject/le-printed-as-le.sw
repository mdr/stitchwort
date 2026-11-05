-- expect-error: E-TYPE-MISMATCH
-- The two types are too long to show whole, and differ only in `<=` against
-- `<`. The note names the whole comparisons, so it shows the `<=` written,
-- not the `Succ` its unfolding has.

import Std (List)

theorem countBelow (width height depth slope: Nat) (firstRows secondRows thirdRows: List Nat)
    (h: List.count (List.takeWhile (List.rangeFrom width 1) (n => n * slope <= height)) (n => n < List.length firstRows + List.length secondRows + List.length thirdRows + depth) = List.length firstRows + List.length secondRows + List.length thirdRows + depth):
    List.count (List.takeWhile (List.rangeFrom width 1) (n => n * slope < height)) (n => n < List.length firstRows + List.length secondRows + List.length thirdRows + depth) = List.length firstRows + List.length secondRows + List.length thirdRows + depth :=
  h

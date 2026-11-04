-- expect-error: E-TYPE-MISMATCH
-- Both types are too long to show whole, so the message shortens them to
-- `…` in the place where they differ (`n < height` against `n <= height`).
-- A note names that place.

import Std (List)

theorem countBelow (width height depth: Nat) (firstRows secondRows thirdRows: List Nat)
    (h: List.count (List.takeWhile (List.rangeFrom width 1) (n => n < height)) (n => n < List.length firstRows + List.length secondRows + List.length thirdRows + depth) = List.length firstRows + List.length secondRows + List.length thirdRows + depth):
    List.count (List.takeWhile (List.rangeFrom width 1) (n => n <= height)) (n => n < List.length firstRows + List.length secondRows + List.length thirdRows + depth) = List.length firstRows + List.length secondRows + List.length thirdRows + depth :=
  h

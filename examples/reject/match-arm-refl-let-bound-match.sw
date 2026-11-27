-- expect-error: E-REFL
-- SW-4910: a false `byComputing` in the arms of a `match` proving an
-- equation over a let-bound `match` is refused by the elaborator, not left
-- for the kernel (the fuzzer's oracle 3).
theorem t (b: Bool): b = b :=
  let pick: Nat := match b with
    | True => 2
    | False => 2
  let same: pick = 0 := match b with
    | True => byComputing
    | False => byComputing
  byComputing

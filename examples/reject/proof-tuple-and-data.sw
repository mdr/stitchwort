-- expect-error: E-TYPE-MISMATCH
-- A tuple whose first part is a proof proves `∧`, so its second part must
-- be a proof too: a pair's parts are never proofs.
def mixed (h: 1 = 1): Nat :=
  let both := (h, 2)
  2

-- expect-error: E-TYPE-MISMATCH
-- SW-3742: a proof-tuple `let` whose right side is wrong reports that error
-- once. The pattern `let`s around it are matches the compiler makes, and
-- their names are bound by the arms whether the goal changes or not, so
-- they don't each warn that their `match` found nothing in the goal.
theorem cascade (h: 1 = 1): 1 = 1 :=
  let (a, b) := (h, h)
  let (c, d) := (a, b)
  let (e, f) := (c, d)
  let (g, i) := (e, 2)
  g

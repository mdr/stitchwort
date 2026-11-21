-- `cases then byFacts`: `byFacts` is checked once per case, and finds a
-- different term in each (`t x`, `f y`); `check --expand-facts` leaves the
-- call as it is and says so (crates/cli/tests/running/facts_expand.rs).

theorem splitB ∀ (b: Bool) (g: Bool → Prop) (p q: Prop) (x: p) (y: q) (t: p → g True) (f: q → g False): g b :=
  cases then byFacts

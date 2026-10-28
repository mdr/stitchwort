-- Binary search over the numbers from `low` up to `high`, for the first at
-- which a test fails, as Rust's `slice::partition_point`. Without knowing
-- anything about the test, the answer is one at which it fails right after
-- one at which it holds (`Nat.partitionPointBounds`); when the test holds up
-- to some point and fails after it, the answer is that point
-- (`Nat.partitionPointSpec`).

-- The first number from `low` up to, not including, `high` at which `p`
-- fails, if `p` holds before it and fails after; `high` if `p` holds
-- throughout. Each step halves the range, so `p` is tried about
-- log2 (high - low) times.
def Nat.partitionPoint (low: Nat) (high: Nat) (p: Nat → Bool): Nat
    decreasing high - low :=
  if apart: low < high then
    let middle := (low + high) / 2
    if p middle then Nat.partitionPoint (middle + 1) high p [decreasing := omega [apart]]
    else Nat.partitionPoint low middle p [decreasing := omega [apart]]
  else low

test "the first number at which the test fails" := Nat.partitionPoint 0 10 (n => n < 7) == 7
test "high when the test never fails" := Nat.partitionPoint 3 10 (n => True) == 10
test "low when the test fails at once" := Nat.partitionPoint 3 10 (n => False) == 3
test "low for an empty range" := Nat.partitionPoint 5 5 (n => n < 7) == 5

-- One step of the search: a halving while the range is not empty...
theorem Nat.partitionPointSplit (low: Nat) (high: Nat) (p: Nat → Bool) (apart: Nat.leq (Succ low) high = True):
    Nat.partitionPoint low high p
      = (if p ((low + high) / 2) then Nat.partitionPoint ((low + high) / 2 + 1) high p else Nat.partitionPoint low ((low + high) / 2) p) :=
  rewrite Nat.partitionPoint.unfold low high p in
    Decidable.elimEq _ _ _ _ (isApart => rfl) (notApart => Void.exfalso (notApart apart))

-- ...and `low` once it is.
theorem Nat.partitionPointDone (low: Nat) (high: Nat) (p: Nat → Bool) (close: Nat.leq (Succ low) high = False): Nat.partitionPoint low high p = low :=
  rewrite Nat.partitionPoint.unfold low high p in
    Decidable.elimEq _ _ _ _ (isApart => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym close) isApart))) (notApart => rfl)

-- For any test: the answer is from `low` to `high`; `p` holds just before
-- it, unless it is `low`; and `p` fails at it, unless it is `high`.
theorem Nat.partitionPointBounds (low: Nat) (high: Nat) (p: Nat → Bool) (ordered: low ≤ high):
    And (low ≤ Nat.partitionPoint low high p)
      (And (Nat.partitionPoint low high p ≤ high)
        (And (Or (Nat.partitionPoint low high p = low) (p (Nat.partitionPoint low high p - 1) = True))
          (Or (Nat.partitionPoint low high p = high) (p (Nat.partitionPoint low high p) = False))))
    decreasing high - low :=
  match apart: Nat.leq (Succ low) high with
    | True =>
      let middle := (low + high) / 2
      rewrite Nat.partitionPointSplit low high p apart in
        match held: p middle with
          | True =>
            let (Both above (Both below (Both before after))) := Nat.partitionPointBounds (middle + 1) high p (omega [apart])
              [decreasing := omega [apart]]
            let found := Nat.partitionPoint (middle + 1) high p
            Both (omega [above])
              (Both below
                (Both
                  (match before with
                    | Inr holds => Inr holds
                    | Inl first =>
                      let previous: found - 1 = middle := omega [first]
                      Inr (rewrite previous in held))
                  after))
          | False =>
            let (Both above (Both below (Both before after))) := Nat.partitionPointBounds low middle p (omega [apart])
              [decreasing := omega [apart]]
            let found := Nat.partitionPoint low middle p
            Both above
              (Both (omega [below, apart])
                (Both before
                  (match after with
                    | Inr fails => Inr fails
                    | Inl last => Inr (rewrite last in held))))
    | False => rewrite Nat.partitionPointDone low high p apart in Both (Nat.leRefl low) (Both ordered (Both (Inl rfl) (Inl (omega [ordered, apart]))))

-- When `p` holds up to some point and fails after it, the answer is that
-- point: `p` holds at every number from `low` before it, and fails at every
-- number from it up to `high`.
theorem Nat.partitionPointSpec (low: Nat) (high: Nat) (p: Nat → Bool) (ordered: low ≤ high)
    (monotone: (smaller: Nat) → (larger: Nat) → smaller ≤ larger → p larger = True → p smaller = True):
    And ((n: Nat) → low ≤ n → n < Nat.partitionPoint low high p → p n = True)
      ((n: Nat) → Nat.partitionPoint low high p ≤ n → n < high → p n = False) :=
  let (Both above (Both below (Both before after))) := Nat.partitionPointBounds low high p ordered
  let found := Nat.partitionPoint low high p
  Both
    (n atLeast under =>
      match before with
        | Inl first => Void.exfalso (omega [first, atLeast, under])
        | Inr holds => monotone n (found - 1) (omega [under]) holds)
    (n atLeast under =>
      match after with
        | Inl last => Void.exfalso (omega [last, atLeast, under])
        | Inr fails =>
          match held: p n with
            | False => rfl
            | True => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym fails) (monotone found n atLeast held))))

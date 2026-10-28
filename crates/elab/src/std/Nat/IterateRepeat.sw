-- What an iteration does after it repeats a value: it cycles through the
-- values before the repeat, so a partial step (`Option.flatMap step`) that
-- repeats a state never stops.

-- `m + n` steps are `m` steps, then `n`.
theorem Nat.iterateAdd (f: a → a): (m: Nat) → (n: Nat) → (x: a) → Nat.iterate (m + n) f x = Nat.iterate n f (Nat.iterate m f x)
  | Zero, n, x => rfl
  | Succ m, n, x => Nat.iterateAdd f m n (f x)

-- A value `f` leaves alone stays.
theorem Nat.iterateFixed (f: a → a) (z: a) (fixed: f z = z): (n: Nat) → Nat.iterate n f z = z
  | Zero => rfl
  | Succ n => rewrite fixed in Nat.iterateFixed f z fixed n

-- Reached at `steps`, a value `f` leaves alone is there at every later step.
theorem Nat.iterateFixedLater (f: a → a) (x: a) (z: a) (fixed: f z = z) (steps: Nat) (later: Nat)
    (reached: Nat.iterate steps f x = z) (le: steps ≤ later): Nat.iterate later f x = z :=
  let split: later = steps + (later - steps) := omega [le]
  rewrite split, Nat.iterateAdd f steps (later - steps) x, reached in Nat.iterateFixed f z fixed (later - steps)

-- With the same value at `first` and at a later `second`, every value is
-- one of the first `second`.
theorem Nat.iterateRepeats (f: a → a) (x: a) (first: Nat) (second: Nat) (earlier: first < second)
    (same: Nat.iterate first f x = Nat.iterate second f x) (n: Nat):
    Exists Nat (m => And (m < second) (Nat.iterate n f x = Nat.iterate m f x))
    decreasing n
:=
  match late: Nat.leq second n with
    | False => Witness n (Both (omega [late]) rfl)
    | True =>
      let back := first + (n - second)
      let shifted: Nat.iterate n f x = Nat.iterate back f x :=
        calc Nat.iterate n f x
          _ = Nat.iterate (second + (n - second)) f x := rewrite (omega [late]: second + (n - second) = n) in rfl
          _ = Nat.iterate (n - second) f (Nat.iterate second f x) := Nat.iterateAdd f second (n - second) x
          _ = Nat.iterate (n - second) f (Nat.iterate first f x) := rewrite same in rfl
          _ = Nat.iterate back f x := Eq.sym (Nat.iterateAdd f first (n - second) x)
      Exists.elim (Nat.iterateRepeats f x first second earlier same back [decreasing := omega [earlier, late]]) (m both =>
        Witness m (Both (And.left both) (Eq.trans shifted (And.right both))))

-- A partial step iterated: a state repeated at `first` and a later
-- `second`, and not stopped by `second`, never stops.
theorem Nat.iterateRepeatNeverNone (step: a → Option a) (start: Option a) (first: Nat) (second: Nat) (earlier: first < second)
    (same: Nat.iterate first (state => Option.flatMap state step) start = Nat.iterate second (state => Option.flatMap state step) start)
    (still: Not (Nat.iterate second (state => Option.flatMap state step) start = None)) (n: Nat):
    Not (Nat.iterate n (state => Option.flatMap state step) start = None) :=
  stopped =>
    Exists.elim (Nat.iterateRepeats (state => Option.flatMap state step) start first second earlier same n) (m both =>
      still
        (Nat.iterateFixedLater (state => Option.flatMap state step) start None rfl m second (Eq.trans (Eq.sym (And.right both)) stopped)
          (omega [And.left both])))

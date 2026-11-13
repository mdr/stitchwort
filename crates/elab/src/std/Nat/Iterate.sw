--| `Nat.iterate`: apply a function n times.
-- A file of its own, so a program that only iterates doesn't check the
-- arithmetic lemmas.

--| `Nat.iterate n f x` is `f` applied `n` times to `x`: `Nat.iterate 3 f x` is
--| `f (f (f x))`. Written with `n.iterate f x` too.
@[tailrec]
def Nat.iterate (count: Nat) (step: a → a) (seed: a): a := match count with
  | Zero => seed
  | Succ n => Nat.iterate n step (step seed)

--| One more step is a step first.
theorem Nat.iterateSucc (n: Nat) (f: a → a) (x: a): Nat.iterate (Succ n) f x = Nat.iterate n f (f x) := rfl

--| One more step is a step last.
theorem Nat.iterateSuccLast (f: a → a) (n: Nat) (x: a): Nat.iterate (Succ n) f x = f (Nat.iterate n f x) :=
  match n with
    | Zero => rfl
    | Succ n => Nat.iterateSuccLast f n (f x)

--| Iterating two functions that agree everywhere gives the same result.
theorem Nat.iterateCong (count: Nat) (f1 f2: a → a) (seed: a) (same: ∀ (x: a) => f1 x = f2 x): Nat.iterate count f1 seed = Nat.iterate count f2 seed :=
  match count with
    | Zero => rfl
    | Succ n => rewrite same seed, Nat.iterateCong n f1 f2 (f2 seed) same

--| A property every step keeps holds after any number of steps.
theorem Nat.iterateKeeps (f: a → a) (keep: a → Prop) (kept: ∀ (x: a) => keep x → keep (f x)) (n: Nat) (x: a) (h: keep x): keep (Nat.iterate n f x) :=
  match n with
    | Zero => h
    | Succ n => Nat.iterateKeeps f keep kept n (f x) (kept x h)

test "Nat.iterate" := Nat.iterate 3 (* 2) 1 == 8 ∧ Nat.iterate 0 (* 2) 5 == 5
test "Nat.iterate dot" := (2: Nat).iterate (x => Text.append x "!") "hi" == "hi!!"

--| Apply `step` until it changes nothing: `Nat.iterateUntilStable x step
--| measure shrinks` is the first `Nat.iterate k step x` with `step` of it
--| equal to it. The loop may not end in general, so it takes what makes it
--| end: a `measure` that `shrinks` at every step that changes something.
--| Needs `DecEq` to see that nothing changed. A simulation reads:
--| `Nat.iterateUntilStable grid step size proof`.
@[tailrec]
def Nat.iterateUntilStable [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: ∀ (y: a) => step y ≠ y → measure (step y) < measure y): a
    decreasing measure x
:=
  if h: step x = x
  then x
  else Nat.iterateUntilStable (step x) step measure shrinks [decreasing := shrinks x h]

--| A value `step` leaves alone is already the answer.
theorem Nat.iterateUntilStableStable [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: ∀ (y: a) => step y ≠ y → measure (step y) < measure y) (h: step x = x):
    Nat.iterateUntilStable x step measure shrinks = x :=
  rewrite Nat.iterateUntilStable.unfold x step measure shrinks in
  Decidable.elimEq (DecEq.decide (step x) x) (y => x) (n => Nat.iterateUntilStable (step x) step measure shrinks) x (y => rfl) (n => Void.exfalso (n h))

--| A value `step` changes goes on from the changed value.
theorem Nat.iterateUntilStableStep [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: ∀ (y: a) => step y ≠ y → measure (step y) < measure y) (h: step x ≠ x):
    Nat.iterateUntilStable x step measure shrinks = Nat.iterateUntilStable (step x) step measure shrinks :=
  rewrite Nat.iterateUntilStable.unfold x step measure shrinks in
  Decidable.elimEq (DecEq.decide (step x) x) (y => x) (n => Nat.iterateUntilStable (step x) step measure shrinks) (Nat.iterateUntilStable (step x) step measure shrinks) (y => Void.exfalso (h y)) (n => rfl)

--| What it returns is a fixed point: `step` leaves it alone.
theorem Nat.iterateUntilStableFixed [auto eq: DecEq a] (x: a) (step: a → a) (measure: a → Nat)
    (shrinks: ∀ (y: a) => step y ≠ y → measure (step y) < measure y):
    step (Nat.iterateUntilStable x step measure shrinks) = Nat.iterateUntilStable x step measure shrinks
    decreasing measure x
:=
  if same: step x = x
  then rewrite Nat.iterateUntilStableStable x step measure shrinks same in same
  else
    rewrite Nat.iterateUntilStableStep x step measure shrinks same in
    Nat.iterateUntilStableFixed (step x) step measure shrinks [decreasing := shrinks x same]

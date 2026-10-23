-- `Iff` ("if and only if") and `Exists` ("for some"): two more ways to build
-- a proposition, beside `And` and `Or` in the core. A file of its own, so
-- that programs that never state these don't check them.

-- Each of `p` and `q` follows from the other.
type Iff (p: Prop) (q: Prop): Prop = {
  forward: p -> q,
  backward: q -> p
}

theorem Iff.refl (p: Prop): Iff p p := { forward = x => x, backward = x => x }

theorem Iff.symm [p q: Prop] (h: Iff p q): Iff q p := { forward = h.backward, backward = h.forward }

theorem Iff.trans [p q r: Prop] (h: Iff p q) (k: Iff q r): Iff p r :=
  { forward = x => k.forward (h.forward x), backward = x => h.backward (k.backward x) }

-- Some value of `a` satisfies `p`: a witness, and a proof that it does.
-- `Exists (n => n * n = 49)` says there is a number whose square is 49.
type Exists (a: Type) (p: a -> Prop): Prop =
  | Witness (value: a) (proof: p value)

-- To prove a proposition from `Exists a p`, take the witness apart: the goal
-- must follow for every value and proof of `p` it might be.
theorem Exists.elim [p: a -> Prop] [goal: Prop] (h: Exists a p) (use: (x: a) -> p x -> goal): goal :=
  match h with
    | Witness x proof => use x proof

-- If something satisfies `p`, it's not the case that nothing does.
theorem Exists.notNone [p: a -> Prop] (some: Exists a p) (none: (x: a) -> Not (p x)): Void :=
  Exists.elim some none

-- A witness for `q` wherever there was one for `p`.
theorem Exists.map [p: a -> Prop] [q: a -> Prop] (f: (x: a) -> p x -> q x) (h: Exists a p): Exists a q :=
  match h with
    | Witness x proof => Witness x (f x proof)

-- Examples ------------------------------------------------------------------

theorem Iff.example: Iff (1 + 1 = 2) (2 = 1 + 1) := { forward = Eq.sym, backward = Eq.sym }

theorem Iff.applyExample: 2 = 1 + 1 := Iff.forward Iff.example rfl

theorem Iff.transExample: Iff (1 + 1 = 2) (1 + 1 = 2) := Iff.trans Iff.example (Iff.symm Iff.example)

theorem Exists.example: Exists Nat ((n: Nat) => n * n = 49) := Witness 7 rfl

theorem Exists.mapExample: Exists Nat ((n: Nat) => n = 3) -> Exists Nat ((n: Nat) => n + 1 = 4) :=
  h => Exists.map ((n: Nat) (e: n = 3) => (rewrite e in rfl: n + 1 = 4)) h

theorem Exists.elimExample: Exists Nat ((n: Nat) => n = 3) -> Exists Nat ((n: Nat) => n + 1 = 4) :=
  h => Exists.elim h ((n: Nat) (e: n = 3) => (Witness 3 rfl: Exists Nat ((m: Nat) => m + 1 = 4)))

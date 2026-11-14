--| Examples of `Iff` and `Exists`, whose lemmas are in the core: `Iff.refl`,
--| `Iff.symm`, `Iff.trans`, `Exists.elim`, `Exists.map` and `Exists.notNone`.
-- A file of its own, so that programs that never state these don't check
-- them. The lemmas themselves are in the core because the library's
-- readings state `∃` and a dot call `x.trans` or `x.map` names every file
-- with such a function in a core namespace, so lemmas here were loaded by
-- any program with a `.trans` call (`Ord.sw`'s `ord.trans`).

-- Examples ------------------------------------------------------------------

theorem Iff.example: (1 + 1 = 2) ↔ (2 = 1 + 1) := { forward = Eq.sym, backward = Eq.sym }

theorem Iff.applyExample: 2 = 1 + 1 := Iff.forward Iff.example rfl

theorem Iff.transExample: (1 + 1 = 2) ↔ (1 + 1 = 2) := Iff.trans Iff.example (Iff.symm Iff.example)

theorem Exists.example: Exists Nat ((n: Nat) => n * n = 49) := Witness 7 rfl

theorem Exists.mapExample: Exists Nat ((n: Nat) => n = 3) → Exists Nat ((n: Nat) => n + 1 = 4) := h =>
  Exists.map ((n: Nat) (e: n = 3) => (rewrite e in rfl: n + 1 = 4)) h

theorem Exists.elimExample: Exists Nat ((n: Nat) => n = 3) → Exists Nat ((n: Nat) => n + 1 = 4) := h =>
  Exists.elim h ((n: Nat) (e: n = 3) => (Witness 3 rfl: Exists Nat ((m: Nat) => m + 1 = 4)))

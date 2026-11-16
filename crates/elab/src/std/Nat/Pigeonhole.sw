--| The pigeonhole principle, for values numbered below a bound: a finite
--| set of states is numbered by an injection into `Nat`, and two of any
--| `n + 1` states below `n` are the same.

--| `f` takes `n + 1` values below `n` at `0, …, n`, so two of them are equal.
-- If none of the first `n` equals the last value, swap the values `n - 1`
-- and `f n` in them: they are then all below `n - 1`.
theorem Nat.pigeonhole ∀ (n: Nat) (f: Nat → Nat)
    (small: ∀ (i: Nat) => i ≤ n → f i < n):
    Exists Nat (i => Exists Nat (j => (i < j) ∧ ((j ≤ n) ∧ (f i = f j)))) :=
  match n with
    | Zero => Void.impossible (arithmetic [small 0 byComputing])
    | Succ n =>
      match found: (List.range 0 (Succ n)).any (i => f i == f (Succ n)) with
        | True =>
          let Witness i (Both inRange hit) := found
          Witness i (Witness (Succ n) (Both (arithmetic) (Both (Nat.leRefl (Succ n)) hit.read)))
        | False =>
          let missed: ∀ (i: Nat) => i ≤ n → f i ≠ f (Succ n) := i le =>
            (found.read i (List.memRangeFromIntro i (Succ n) 0 (Nat.zeroLe i) (arithmetic [le]))).read
          let swapped := (i: Nat) => if f i == n then f (Succ n) else f i
          let swappedSmall: ∀ (i: Nat) => i ≤ n → swapped i < n := i le =>
            match atLast: f i == n with
              | True =>
                let notLast: f (Succ n) ≠ n := same => missed i le (Eq.trans atLast.read same.flipped)
                arithmetic [small (Succ n) (Nat.leRefl (Succ n)), notLast]
              | False => arithmetic [small i (arithmetic [le]), atLast]
          Exists.elim (Nat.pigeonhole n swapped swappedSmall) (i rest =>
            Exists.elim rest (j both =>
              let ij := both.left
              let jLast := both.right.left
              let same := both.right.right
              let agree: f i = f j := match atI: f i == n, atJ: f j == n with
                | True, True => Eq.trans atI.read atJ.read.flipped
                | True, False => (missed j jLast same.flipped).impossible
                | False, True => Void.impossible (missed i (arithmetic [ij, jLast]) same)
                | False, False => same
              Witness i (Witness j (Both ij (Both (arithmetic [jLast]) agree)))))

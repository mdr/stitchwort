--| The pigeonhole principle, for values numbered below a bound: a finite
--| set of states is numbered by an injection into `Nat`, and two of any
--| `n + 1` states below `n` are the same.

--| `f` takes `n + 1` values below `n` at `0, …, n`, so two of them are equal.
-- If none of the first `n` equals the last value, swap the values `n - 1`
-- and `f n` in them: they are then all below `n - 1`.
theorem Nat.pigeonhole (n: Nat) (f: Nat → Nat) (small: ∀ (i: Nat) => i ≤ n → f i < n):
    Exists Nat (i => Exists Nat (j => (i < j) ∧ ((j ≤ n) ∧ (f i = f j)))) := match n with
      | Zero => Void.exfalso (omega [small 0 rfl])
      | Succ n =>
        match found: (List.range 0 (Succ n)).any (i => f i == f (Succ n)) with
          | True =>
            let Witness i (Both inRange hit) := found
            Witness i (Witness (Succ n) (Both (omega) (Both (Nat.leRefl (Succ n)) hit.read)))
          | False =>
            let missed: ∀ (i: Nat) => i ≤ n → f i ≠ f (Succ n) :=
              i le =>
                (found.read i (List.memRangeFromIntro i (Succ n) 0 (Nat.zeroLe i) (omega [le]))).read
            let swapped := (i: Nat) => if f i == n then f (Succ n) else f i
            let swappedSmall: ∀ (i: Nat) => i ≤ n → swapped i < n :=
              i le =>
                match atLast: f i == n with
                  | True =>
                    let notLast: f (Succ n) ≠ n := same => missed i le (Eq.trans atLast.read (Eq.sym same))
                    omega [small (Succ n) (Nat.leRefl (Succ n)), notLast]
                  | False => omega [small i (omega [le]), atLast.read]
            Exists.elim (Nat.pigeonhole n swapped swappedSmall) (i rest =>
              Exists.elim rest (j both =>
                let ij := And.left both
                let jLast := And.left (And.right both)
                let same := And.right (And.right both)
                let agree: f i = f j :=
                  match atI: f i == n, atJ: f j == n with
                    | True, True => Eq.trans atI.read (Eq.sym atJ.read)
                    | True, False => Void.exfalso (missed j jLast (Eq.sym same))
                    | False, True => Void.exfalso (missed i (omega [ij, jLast]) same)
                    | False, False => same
                Witness i (Witness j (Both ij (Both (omega [jLast]) agree)))))

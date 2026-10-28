-- The pigeonhole principle, for values numbered below a bound: a finite
-- set of states is numbered by an injection into `Nat`, and two of any
-- `n + 1` states below `n` are the same.

-- `f` takes `n + 1` values below `n` at `0, …, n`, so two of them are equal.
-- If none of the first `n` equals the last value, swap the values `n - 1`
-- and `f n` in them: they are then all below `n - 1`.
theorem Nat.pigeonhole: (n: Nat) → (f: Nat → Nat) → ((i: Nat) → i ≤ n → f i < n) →
    Exists Nat (i => Exists Nat (j => And (i < j) (And (j ≤ n) (f i = f j))))
  | Zero, f, small => Void.exfalso (omega [small 0 rfl])
  | Succ n, f, small =>
    match found: (List.range (Succ n)).any (i => f i == f (Succ n)) with
      | True =>
        List.anyTrueElim (List.range (Succ n)) (i => f i == f (Succ n))
          (Exists Nat (i => Exists Nat (j => And (i < j) (And (j ≤ Succ n) (f i = f j))))) found
          (i inRange hit =>
            Witness i
              (Witness (Succ n)
                (Both (omega [And.right (List.memRangeFrom i (Succ n) 0 inRange)])
                  (Both (Nat.leRefl (Succ n)) (DecEq.sound (f i) (f (Succ n)) hit)))))
      | False =>
        let missed: (i: Nat) → i ≤ n → Not (f i = f (Succ n)) :=
          i le same =>
            Bool.falseNotTrue
              (Eq.trans (Eq.sym found)
                (List.anyOfMem (List.range (Succ n)) (i => f i == f (Succ n)) i (rewrite same in DecEq.refl (f (Succ n)))
                  (List.memRangeFromIntro i (Succ n) 0 (Nat.zeroLe i) (omega [le]))))
        let swapped := (i: Nat) => if f i == n then f (Succ n) else f i
        let swappedSmall: (i: Nat) → i ≤ n → swapped i < n :=
          i le =>
            match atLast: f i == n with
              | True =>
                let notLast: Not (f (Succ n) = n) := same => missed i le (Eq.trans (DecEq.sound (f i) n atLast) (Eq.sym same))
                omega [small (Succ n) (Nat.leRefl (Succ n)), notLast]
              | False => omega [small i (omega [le]), DecEq.soundFalse (f i) n atLast]
        Exists.elim (Nat.pigeonhole n swapped swappedSmall) (i rest =>
          Exists.elim rest (j both =>
            let ij := And.left both
            let jLast := And.left (And.right both)
            let same := And.right (And.right both)
            let agree: f i = f j :=
              match atI: f i == n, atJ: f j == n with
                | True, True => Eq.trans (DecEq.sound (f i) n atI) (Eq.sym (DecEq.sound (f j) n atJ))
                | True, False => Void.exfalso (missed j jLast (Eq.sym same))
                | False, True => Void.exfalso (missed i (omega [ij, jLast]) same)
                | False, False => same
            Witness i (Witness j (Both ij (Both (omega [jLast]) agree)))))

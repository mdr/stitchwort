--| Facts about `Range`, kept out of the program so that running a day does
--| not check them: day 2 uses the two about runs of ids, day 5 the counting
--| lemmas.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Nat, Ordering, Void)

--| Which ids from `from` to `to` lie in the run `List.rangeFrom (to + 1 - from) from`.

-- Counting the ids that ranges hold, for example to show that disjoint ranges
-- add up (day 5 uses these in `Aoc.Year2025.Day05.solvePart2Correct`).

theorem containsLo ∀ (r: Range) (id: Nat) (h: r.contains id = True): r.from ≤ id := Nat.betweenLo r.from r.to id h

theorem containsHi ∀ (r: Range) (id: Nat) (h: r.contains id = True): id ≤ r.to := Nat.betweenHi r.from r.to id h

--| How many of the `c` ids from `s` the range holds.
theorem countFrom ∀ (r: Range) (c s: Nat)
    (h: r.to < s + c):
    List.occurrences (List.rangeFrom c s) (id => r.contains id) = Succ r.to - Nat.max r.from s :=
  match c with
    | Zero => arithmetic
    | Succ c =>
      match t: Nat.leq r.from s, i: Nat.leq s r.to with
        | True, True =>
          -- (`t` and `i` are True, so the match has already counted the first id, and `max from s` is `s`)
          calc Succ (List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id))
            _ = Succ (Succ r.to - Nat.max r.from (Succ s)) := rewrite countFrom r c (Succ s) arithmetic
            _ = Succ r.to - s := arithmetic
        | True, False =>
          -- (`i` is False, so the match has already dropped the first id from the goal, and `max from s` is `s`)
          calc List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id)
            _ = Succ r.to - Nat.max r.from (Succ s) := countFrom r c (Succ s) arithmetic
            _ = Succ r.to - s := arithmetic
        | False, _ =>
          -- (the match has already replaced the first id's test by `False`)
          calc List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id)
            _ = Succ r.to - Nat.max r.from (Succ s) := countFrom r c (Succ s) arithmetic
            _ = Succ r.to - r.from := arithmetic

--| A range ending below `n` holds `size` of the ids below `n`.
theorem countBelow ∀ (r: Range) (n: Nat)
    (h: r.to < n):
    List.occurrences (List.range 0 n) (id => r.contains id) = r.size :=
  calc List.occurrences (List.range 0 n) (id => r.contains id)
    _ = Succ r.to - Nat.max r.from 0 := countFrom r n 0 h
    _ = r.size := arithmetic

--| An empty range (it ends before it starts) holds no ids, and has size 0.
theorem countEmpty ∀ (r: Range)
    (e: Nat.leq r.from r.to = False) (ids: List Nat):
    ids.occurrences (id => r.contains id) = r.size :=
  calc List.occurrences ids (id => r.contains id)
    _ = 0 := List.occurrencesNone ids (id => r.contains id) (id =>
      match t: Nat.leq r.from id with
        | True => Nat.leqFalseOfLess r.to id arithmetic
        | False => byComputing)
    _ = r.size := arithmetic

--| The derived order on ranges (by start, then end) puts the smaller start first.
theorem compareFrom ∀ (a b: Range) (h: Ordering.isLessEq (Ord.compare a b) = True): a.from ≤ b.from := match a, b with
  | { from = f1, to = t1 }, { from = f2, to = t2 } =>
    match e: Nat.compare f1 f2 with
      | Less => Nat.leOfCompare f1 f2 (g => Ordering.lessNotGreater (Eq.trans e.flipped g))
      | Equal => Nat.leOfCompare f1 f2 (g => Ordering.equalNotGreater (Eq.trans e.flipped g))

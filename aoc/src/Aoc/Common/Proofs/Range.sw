-- Facts about `Range`, kept out of the program so that running a day does
-- not check them: day 2 uses the two about runs of ids, day 5 the counting
-- lemmas.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Bool, Eq, List, Nat, Ordering, Void)

-- Which ids from `from` to `to` lie in the run `List.rangeFrom (to + 1 - from) from`.
theorem rangeEnd (from: Nat) (to: Nat) (x: Nat) (h1: from <= x) (h2: x < from + (to + 1 - from)): x <= to :=
  omega

theorem rangeIn (from: Nat) (to: Nat) (y: Nat) (h1: from <= y) (h2: y <= to): y < from + (to + 1 - from) :=
  omega

-- Counting the ids that ranges hold, for example to show that disjoint ranges
-- add up (day 5 uses these in `Aoc.Day05.solvePart2Correct`).

theorem containsLo (r: Range) (id: Nat) (h: r.contains id = True): r.from <= id := Nat.betweenLo r.from r.to id h

theorem containsHi (r: Range) (id: Nat) (h: r.contains id = True): id <= r.to := Nat.betweenHi r.from r.to id h

-- How many of the `c` ids from `s` the range holds.
theorem countFrom (r: Range): (c: Nat) -> (s: Nat) -> r.to < s + c ->
    List.occurrences (List.rangeFrom c s) (id => r.contains id) = Succ r.to - Nat.max r.from s
  | Zero, s, h =>
    omega
  | Succ c, s, h =>
    match t: Nat.leq r.from s, i: Nat.leq s r.to with
      | True, True =>
        -- (`t` and `i` are True, so the match has already counted the first id, and `max from s` is `s`)
        calc Succ (List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id))
          _ = Succ (Succ r.to - Nat.max r.from (Succ s))
            := rewrite countFrom r c (Succ s) omega
          _ = Succ r.to - s := omega
      | True, False =>
        -- (`i` is False, so the match has already dropped the first id from the goal, and `max from s` is `s`)
        calc List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id)
          _ = Succ r.to - Nat.max r.from (Succ s)
            := countFrom r c (Succ s) omega
          _ = Succ r.to - s := omega
      | False, _ =>
        -- (the match has already replaced the first id's test by `False`)
        calc List.occurrences (List.rangeFrom c (Succ s)) (id => r.contains id)
          _ = Succ r.to - Nat.max r.from (Succ s)
            := countFrom r c (Succ s) omega
          _ = Succ r.to - r.from := omega

-- A range ending below `n` holds `size` of the ids below `n`.
theorem countBelow (r: Range) (n: Nat) (h: r.to < n): List.occurrences (List.range n) (id => r.contains id) = r.size :=
  calc List.occurrences (List.range n) (id => r.contains id)
    _ = Succ r.to - Nat.max r.from 0 := countFrom r n 0 h
    _ = r.size := omega

-- An empty range (it ends before it starts) holds no ids, and has size 0.
theorem countEmpty (r: Range) (e: Nat.leq r.from r.to = False) (ids: List Nat): List.occurrences ids (id => r.contains id) = r.size :=
  calc List.occurrences ids (id => r.contains id)
    _ = 0 := List.occurrencesNone ids
      (id => r.contains id)
      (id =>
        match t: Nat.leq r.from id with
          | True => Nat.leqFalseOfLess r.to id omega
          | False => rfl)
    _ = r.size := omega

-- The derived order on ranges (by start, then end) puts the smaller start first.
theorem compareFrom: (a: Range) -> (b: Range) -> Ordering.isLessEq (Ord.compare a b) = True -> a.from <= b.from
  | { from = f1, to = t1 }, { from = f2, to = t2 }, h =>
    match e: Nat.compare f1 f2 with
      | Less => Nat.leOfCompare f1 f2 (g => Ordering.lessNotGreater (Eq.trans (Eq.sym e) g))
      | Equal => Nat.leOfCompare f1 f2 (g => Ordering.equalNotGreater (Eq.trans (Eq.sym e) g))
      | Greater => Void.exfalso (Bool.falseNotTrue h)

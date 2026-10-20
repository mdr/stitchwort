-- Facts about `Range`, kept out of the program so that running a day does
-- not check them: day 2 uses the two about runs of ids, day 5 the counting
-- lemmas.

namespace Aoc.Common.Proofs
import Aoc.Common (..)
import Std (Eq)

-- Which ids from `from` to `to` lie in the run `List.rangeFrom (to + 1 - from) from`.
theorem rangeEnd (from: Nat) (to: Nat) (x: Nat) (h1: from <= x) (h2: x < from + (to + 1 - from)): x <= to :=
  match e: Nat.leq from (to + 1) with
    | True =>
      calc x
        _ < from + (to + 1 - from) := h2
        _ = to + 1             := Nat.addSubCancel from (to + 1) e
        _ = Succ to            := Nat.addOne to
    | False =>
      Void.exfalso (Nat.lessIrrefl x
        (calc x
          _ < from + (to + 1 - from) := h2
          _ = from                 := rewrite Nat.subEqZero (to + 1) from (Nat.lessLe (to + 1) from (Nat.leqFalse from (to + 1) e)), Nat.addZero from
          _ <= x                 := h1))

theorem rangeIn (from: Nat) (to: Nat) (y: Nat) (h1: from <= y) (h2: y <= to): y < from + (to + 1 - from) :=
  calc y
    _ < Succ to            := h2
    _ = to + 1             := Eq.sym (Nat.addOne to)
    _ = from + (to + 1 - from) := Eq.sym (Nat.addSubCancel from (to + 1) (Nat.leTrans from y (to + 1) h1 (Nat.leTrans y to (to + 1) h2 (Nat.leCongRight to (Succ to) (to + 1) (Eq.sym (Nat.addOne to)) (Nat.leSucc to)))))

-- Counting the ids that ranges hold, for example to show that disjoint ranges
-- add up (day 5 uses these in `Aoc.Day05.solvePart2Correct`).

theorem containsLo (r: Range) (id: Nat) (h: r.contains id = True): r.from <= id := Nat.betweenLo r.from r.to id h

theorem containsHi (r: Range) (id: Nat) (h: r.contains id = True): id <= r.to := Nat.betweenHi r.from r.to id h

-- How many of the `c` ids from `s` the range holds.
theorem countFrom (r: Range): (c: Nat) -> (s: Nat) -> r.to < s + c ->
    List.occurrences (id => r.contains id) (List.rangeFrom c s) = Succ r.to - Nat.max r.from s
  | Zero,   s, h =>
    Eq.sym (Nat.subEqZero (Succ r.to) (Nat.max r.from s)
      (Nat.leTrans (Succ r.to) s (Nat.max r.from s) (Nat.leCongRight (Succ r.to) (s + 0) s (Nat.addZero s) h) (Nat.leMaxRight r.from s)))
  | Succ c, s, h =>
    match t: Nat.leq r.from s, i: Nat.leq s r.to with
      | True, True =>
        -- (`t` and `i` are True, so the match has already counted the first id, and `max from s` is `s`)
        calc Succ (List.occurrences (id => r.contains id) (List.rangeFrom c (Succ s)))
          _ = Succ (Succ r.to - Nat.max r.from (Succ s))
              := rewrite countFrom r c (Succ s) (Nat.ltCongRight r.to (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = Succ (Succ r.to - Succ s) := rewrite Nat.maxRight r.from (Succ s) (Nat.leTrans r.from s (Succ s) t (Nat.leSucc s))
          _ = Succ r.to - s             := Eq.sym (Nat.subSuccRight s (Succ r.to) i)
      | True, False =>
        -- (`i` is False, so the match has already dropped the first id from the goal, and `max from s` is `s`)
        calc List.occurrences (id => r.contains id) (List.rangeFrom c (Succ s))
          _ = Succ r.to - Nat.max r.from (Succ s)
              := countFrom r c (Succ s) (Nat.ltCongRight r.to (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = 0
              := Nat.subEqZero (Succ r.to) (Nat.max r.from (Succ s))
                   (Nat.leTrans (Succ r.to) (Succ s) (Nat.max r.from (Succ s)) (Nat.lessLe r.to s (Nat.leqFalse s r.to i)) (Nat.leMaxRight r.from (Succ s)))
          _ = Succ r.to - s := Eq.sym (Nat.subEqZero (Succ r.to) s (Nat.leqFalse s r.to i))
      | False, _ =>
        -- (the match has already replaced the first id's test by `False`)
        calc List.occurrences (id => r.contains id) (List.rangeFrom c (Succ s))
          _ = Succ r.to - Nat.max r.from (Succ s)
              := countFrom r c (Succ s) (Nat.ltCongRight r.to (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = Succ r.to - r.from            := rewrite Nat.maxLeft r.from (Succ s) (Nat.leqFalse r.from s t)

-- A range ending below `n` holds `size` of the ids below `n`.
theorem countBelow (r: Range) (n: Nat) (h: r.to < n): List.occurrences (id => r.contains id) (List.range n) = r.size :=
  calc List.occurrences (id => r.contains id) (List.range n)
    _ = Succ r.to - Nat.max r.from 0 := countFrom r n 0 h
    _ = Succ r.to - r.from           := rewrite Nat.maxLeft r.from 0 (Nat.zeroLe r.from)
    _ = r.size                     := rewrite Nat.addOne r.to

-- An empty range (it ends before it starts) holds no ids, and has size 0.
theorem countEmpty (r: Range) (e: Nat.leq r.from r.to = False) (ids: List Nat): List.occurrences (id => r.contains id) ids = r.size :=
  calc List.occurrences (id => r.contains id) ids
    _ = 0 := List.occurrencesNone (id => r.contains id)
          (id =>
            match t: Nat.leq r.from id with
              | True  => Eq.trans (Bool.decTrueToBool (Nat.leq id r.to)) (Nat.leqFalseOfLess r.to id (Nat.leTrans (Succ r.to) r.from id (Nat.leqFalse r.from r.to e) t))
              | False => rfl)
          ids
    _ = r.size := rewrite Nat.addOne r.to, Nat.subEqZero (Succ r.to) r.from (Nat.leqFalse r.from r.to e)

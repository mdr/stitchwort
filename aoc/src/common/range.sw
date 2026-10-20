-- Generic range code, shared between days.

namespace Aoc.Common
import Std (Eq)

-- A range of ids, both ends included: "3-5" is `{ lo = 3, hi = 5 }`.
type Range = { lo: Nat, hi: Nat }

def Range.parse (t: Text): Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

test "parse" := Range.parse "3-5" == Just { lo = 3, hi = 5 }
test "parse junk" := Range.parse "4-x" == Nothing

-- Which ids from lo to hi lie in the run `List.rangeFrom (hi + 1 - lo) lo`.
theorem rangeEnd (lo: Nat) (hi: Nat) (x: Nat) (h1: lo <= x) (h2: x < lo + (hi + 1 - lo)): x <= hi :=
  match e: Nat.leq lo (hi + 1) with
    | True =>
      calc x
        _ < lo + (hi + 1 - lo) := h2
        _ = hi + 1             := Nat.addSubCancel lo (hi + 1) e
        _ = Succ hi            := Nat.addOne hi
    | False =>
      Void.exfalso (Nat.lessIrrefl x
        (calc x
          _ < lo + (hi + 1 - lo) := h2
          _ = lo                 := rewrite Nat.subEqZero (hi + 1) lo (Nat.lessLe (hi + 1) lo (Nat.leqFalse lo (hi + 1) e)), Nat.addZero lo
          _ <= x                 := h1))

theorem rangeIn (lo: Nat) (hi: Nat) (y: Nat) (h1: lo <= y) (h2: y <= hi): y < lo + (hi + 1 - lo) :=
  calc y
    _ < Succ hi            := h2
    _ = hi + 1             := Eq.sym (Nat.addOne hi)
    _ = lo + (hi + 1 - lo) := Eq.sym (Nat.addSubCancel lo (hi + 1) (Nat.leTrans lo y (hi + 1) h1 (Nat.leTrans y hi (hi + 1) h2 (Nat.leCongRight hi (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leSucc hi)))))

def Range.contains (r: Range) (id: Nat): Bool := r.lo <= id && id <= r.hi

test "contains" := (Range.contains { lo = 3, hi = 5 } 3, Range.contains { lo = 3, hi = 5 } 5, Range.contains { lo = 3, hi = 5 } 6) == (True, True, False)

def Range.size (r: Range): Nat := r.hi + 1 - r.lo

test "size" := Range.size { lo = 3, hi = 5 } == 3

-- Counting the ids that ranges hold, for example to show that disjoint ranges
-- add up (day 5 uses these in `Aoc.Day05.solvePart2Correct`).

theorem Range.containsLo (r: Range) (id: Nat) (h: r.contains id = True): r.lo <= id := Nat.betweenLo r.lo r.hi id h

theorem Range.containsHi (r: Range) (id: Nat) (h: r.contains id = True): id <= r.hi := Nat.betweenHi r.lo r.hi id h

-- How many of the `c` ids from `s` the range holds.
theorem Range.countFrom (r: Range): (c: Nat) -> (s: Nat) -> r.hi < s + c ->
    List.occurrences (\id => r.contains id) (List.rangeFrom c s) = Succ r.hi - Nat.max r.lo s
  | Zero,   s, h =>
    Eq.sym (Nat.subEqZero (Succ r.hi) (Nat.max r.lo s)
      (Nat.leTrans (Succ r.hi) s (Nat.max r.lo s) (Nat.leCongRight (Succ r.hi) (s + 0) s (Nat.addZero s) h) (Nat.leMaxRight r.lo s)))
  | Succ c, s, h =>
    match t: Nat.leq r.lo s, i: Nat.leq s r.hi with
      | True, True =>
        -- (`t` and `i` are True, so the match has already counted the first id, and `max lo s` is `s`)
        calc Succ (List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s)))
          _ = Succ (Succ r.hi - Nat.max r.lo (Succ s))
              := rewrite Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = Succ (Succ r.hi - Succ s) := rewrite Nat.maxRight r.lo (Succ s) (Nat.leTrans r.lo s (Succ s) t (Nat.leSucc s))
          _ = Succ r.hi - s             := Eq.sym (Nat.subSuccRight s (Succ r.hi) i)
      | True, False =>
        -- (`i` is False, so the match has already dropped the first id from the goal, and `max lo s` is `s`)
        calc List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s))
          _ = Succ r.hi - Nat.max r.lo (Succ s)
              := Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = 0
              := Nat.subEqZero (Succ r.hi) (Nat.max r.lo (Succ s))
                   (Nat.leTrans (Succ r.hi) (Succ s) (Nat.max r.lo (Succ s)) (Nat.lessLe r.hi s (Nat.leqFalse s r.hi i)) (Nat.leMaxRight r.lo (Succ s)))
          _ = Succ r.hi - s := Eq.sym (Nat.subEqZero (Succ r.hi) s (Nat.leqFalse s r.hi i))
      | False, _ =>
        -- (the match has already replaced the first id's test by `False`)
        calc List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s))
          _ = Succ r.hi - Nat.max r.lo (Succ s)
              := Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)
          _ = Succ r.hi - r.lo            := rewrite Nat.maxLeft r.lo (Succ s) (Nat.leqFalse r.lo s t)

-- A range ending below `n` holds `size` of the ids below `n`.
theorem Range.countBelow (r: Range) (n: Nat) (h: r.hi < n): List.occurrences (\id => r.contains id) (List.range n) = r.size :=
  calc List.occurrences (\id => r.contains id) (List.range n)
    _ = Succ r.hi - Nat.max r.lo 0 := Range.countFrom r n 0 h
    _ = Succ r.hi - r.lo           := rewrite Nat.maxLeft r.lo 0 (Nat.zeroLe r.lo)
    _ = r.size                     := rewrite Nat.addOne r.hi

-- An empty range (it ends before it starts) holds no ids, and has size 0.
theorem Range.countEmpty (r: Range) (e: Nat.leq r.lo r.hi = False) (ids: List Nat): List.occurrences (\id => r.contains id) ids = r.size :=
  calc List.occurrences (\id => r.contains id) ids
    _ = 0 := List.occurrencesNone (\id => r.contains id)
          (\id =>
            match t: Nat.leq r.lo id with
              | True  => Eq.trans (Bool.decTrueToBool (Nat.leq id r.hi)) (Nat.leqFalseOfLess r.hi id (Nat.leTrans (Succ r.hi) r.lo id (Nat.leqFalse r.lo r.hi e) t))
              | False => rfl)
          ids
    _ = r.size := rewrite Nat.addOne r.hi, Nat.subEqZero (Succ r.hi) r.lo (Nat.leqFalse r.lo r.hi e)

def Range.ids (r: Range): List Nat := List.rangeFrom r.size r.lo

test "ids" := Range.ids { lo = 3, hi = 5 } == [3, 4, 5]

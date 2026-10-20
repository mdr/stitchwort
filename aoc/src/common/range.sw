-- Generic range code, shared between days.

namespace Aoc.Common

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
  Bool.inspect (Nat.leq lo (hi + 1)) (\u => x <= hi)
    (\t => Nat.ltCongRight x (lo + (hi + 1 - lo)) (Succ hi) (Eq.trans (Nat.addSubCancel lo (hi + 1) t) (Nat.addOne hi)) h2)
    (\f => Void.exfalso (Nat.lessIrrefl x (Nat.leTrans (Succ x) lo x
      (Nat.ltCongRight x (lo + (hi + 1 - lo)) lo
        (Eq.trans (Eq.cong (\t => lo + t) (Nat.subEqZero (hi + 1) lo (Nat.lessLe (hi + 1) lo (Nat.leqFalse lo (hi + 1) f)))) (Nat.addZero lo)) h2)
      h1)))

theorem rangeIn (lo: Nat) (hi: Nat) (y: Nat) (h1: lo <= y) (h2: y <= hi): y < lo + (hi + 1 - lo) :=
  Nat.ltCongRight y (Succ hi) (lo + (hi + 1 - lo))
    (Eq.trans (Eq.sym (Nat.addOne hi))
      (Eq.sym (Nat.addSubCancel lo (hi + 1) (Nat.leTrans lo y (hi + 1) h1 (Nat.leTrans y hi (hi + 1) h2 (Nat.leCongRight hi (Succ hi) (hi + 1) (Eq.sym (Nat.addOne hi)) (Nat.leSucc hi)))))))
    h2

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
    Bool.inspect (Nat.leq r.lo s) (\u => List.occurrences (\id => r.contains id) (List.rangeFrom (Succ c) s) = Succ r.hi - Nat.max r.lo s)
      (\t => Bool.inspect (Nat.leq s r.hi) (\u => List.occurrences (\id => r.contains id) (List.rangeFrom (Succ c) s) = Succ r.hi - Nat.max r.lo s)
        (\i =>
          Eq.trans (Eq.cong (\b => Bool.toNat b + List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s))) (Nat.betweenYes r.lo r.hi s t i))
            (Eq.trans (Eq.cong (\n => 1 + n) (Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h)))
              (Eq.trans (Eq.cong (\m => 1 + (Succ r.hi - m)) (Nat.maxRight r.lo (Succ s) (Nat.leTrans r.lo s (Succ s) t (Nat.leSucc s))))
                (Eq.trans (Eq.sym (Nat.subSuccRight s (Succ r.hi) i))
                  (Eq.sym (Eq.cong (\m => Succ r.hi - m) (Nat.maxRight r.lo s t)))))))
        (\o =>
          Eq.trans (Eq.cong (\b => Bool.toNat b + List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s))) (Nat.betweenAbove r.lo r.hi s t o))
            (Eq.trans (Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h))
              (Eq.trans
                (Nat.subEqZero (Succ r.hi) (Nat.max r.lo (Succ s))
                  (Nat.leTrans (Succ r.hi) (Succ s) (Nat.max r.lo (Succ s)) (Nat.lessLe r.hi s (Nat.leqFalse s r.hi o)) (Nat.leMaxRight r.lo (Succ s))))
                (Eq.sym (Nat.subEqZero (Succ r.hi) (Nat.max r.lo s)
                  (Nat.leTrans (Succ r.hi) s (Nat.max r.lo s) (Nat.leqFalse s r.hi o) (Nat.leMaxRight r.lo s))))))))
      (\f =>
        Eq.trans (Eq.cong (\b => Bool.toNat b + List.occurrences (\id => r.contains id) (List.rangeFrom c (Succ s))) (Nat.betweenBelow r.lo r.hi s f))
          (Eq.trans (Range.countFrom r c (Succ s) (Nat.ltCongRight r.hi (s + Succ c) (Succ s + c) (Nat.addSucc s c) h))
            (Eq.trans (Eq.cong (\m => Succ r.hi - m) (Nat.maxLeft r.lo (Succ s) (Nat.leqFalse r.lo s f)))
              (Eq.sym (Eq.cong (\m => Succ r.hi - m) (Nat.maxLeft r.lo s (Nat.lessLe s r.lo (Nat.leqFalse r.lo s f))))))))

-- A range ending below `n` holds `size` of the ids below `n`.
theorem Range.countBelow (r: Range) (n: Nat) (h: r.hi < n): List.occurrences (\id => r.contains id) (List.range n) = r.size :=
  Eq.trans (Range.countFrom r n 0 h)
    (Eq.trans (Eq.cong (\m => Succ r.hi - m) (Nat.maxLeft r.lo 0 (Nat.zeroLe r.lo)))
      (Eq.cong (\t => t - r.lo) (Eq.sym (Nat.addOne r.hi))))

-- An empty range (it ends before it starts) holds no ids, and has size 0.
theorem Range.countEmpty (r: Range) (e: Nat.leq r.lo r.hi = False) (ids: List Nat): List.occurrences (\id => r.contains id) ids = r.size :=
  Eq.trans
    (List.occurrencesNone (\id => r.contains id)
      (\id => Bool.inspect (Nat.leq r.lo id) (\u => r.contains id = False)
        (\t => Nat.betweenAbove r.lo r.hi id t (Nat.leqFalseOfLess r.hi id (Nat.leTrans (Succ r.hi) r.lo id (Nat.leqFalse r.lo r.hi e) t)))
        (\f => Nat.betweenBelow r.lo r.hi id f))
      ids)
    (Eq.sym (Eq.trans (Eq.cong (\t => t - r.lo) (Nat.addOne r.hi)) (Nat.subEqZero (Succ r.hi) r.lo (Nat.leqFalse r.lo r.hi e))))

def Range.ids (r: Range): List Nat := List.rangeFrom r.size r.lo

test "ids" := Range.ids { lo = 3, hi = 5 } == [3, 4, 5]

-- SW-147 feasibility prototype: pieces of a proof that part 2's
-- inclusion-exclusion is right. Not wired into `solvePart2`.

namespace Aoc.Day02.Part2Proof
import Aoc.Common (Range, writeTimes, writtenAs, multiplier, writeTimesMul)
import Aoc.Day02 (weight, repeats, bruteSum, range)

-- (0) The weights stop at 10 repeats, so an 11-digit id made of one digit
-- (1 written 11 times) is missed: part 2 is only right for ids of at most
-- 10 digits. The theorem needs that as a hypothesis (or the weights must be
-- the Moebius function for every n).
test "eleven ones are missed" := (Range.invalid weight (range 11111111111 11111111111), bruteSum repeats (range 11111111111 11111111111)) == (0, 11111111111)
test "ten ones are counted" := (Range.invalid weight (range 1111111111 1111111111), bruteSum repeats (range 1111111111 1111111111)) == (1111111111, 1111111111)

-- (1) `all` over a run of numbers: each element passes.
theorem allRangeElim (q: Nat -> Bool): (c: Nat) -> (s: Nat) -> List.all q (List.rangeFrom c s) = True ->
    (k: Nat) -> s <= k -> k < s + c -> q k = True
  | Zero,   s, h, k, h1, h2 => Void.exfalso (Nat.lessIrrefl k (Nat.leTrans (Succ k) s k (Nat.ltCongRight k (s + 0) s (Nat.addZero s) h2) h1))
  | Succ c, s, h, k, h1, h2 =>
    Bool.inspect (q s) (\u => q k = True)
      (\t => Bool.inspect (k == s) (\u => q k = True)
        (\e => J (\z p => q z = True) t (Eq.sym (Decidable.toBoolSound (Nat.decEq k s) e)))
        (\ne => allRangeElim q c (Succ s)
          (Eq.trans (Eq.cong (\b => Bool.ifThenElse b (\u => List.all q (List.rangeFrom c (Succ s))) (\u => False)) (Eq.sym t)) h)
          k (Nat.leNeSucc s k h1 (\e => Bool.trueNotFalse (Eq.trans (Eq.sym (Decidable.toBoolOf (Nat.decEq k s) (Eq.sym e))) ne))) (Nat.ltSuccAdd s c k h2)))
      (\f => Void.exfalso (Bool.trueNotFalse (Eq.trans (Eq.sym h) (Eq.cong (\b => Bool.ifThenElse b (\u => List.all q (List.rangeFrom c (Succ s))) (\u => False)) f))))

-- `(not a) || b` is "a implies b".
theorem implies: (a: Bool) -> (b: Bool) -> (Bool.not a || b) = True -> a = True -> b = True
  | True,  b, h, ha => h
  | False, b, h, ha => Void.exfalso (Bool.falseNotTrue ha)

-- (2) The one non-obvious fact about periods, for 6 digits: digits that are
-- a 3-digit block written twice and a 2-digit block written three times are
-- one digit written six times (abcabc = ababab forces a = b = c). Proved by
-- checking all 90 two-digit blocks.
def sixCheck (c: Nat): Bool :=
  Bool.not (writtenAs (Nat.digits (writeTimes 2 c 3)) 3 2) || writtenAs (Nat.digits (writeTimes 2 c 3)) 1 6

theorem sixChecked: List.all sixCheck (List.rangeFrom 90 10) = True := rfl

theorem sixFromTwoAndThree (c: Nat) (h1: 10 <= c) (h2: c < 100) (h: writtenAs (Nat.digits (writeTimes 2 c 3)) 3 2 = True):
    writtenAs (Nat.digits (writeTimes 2 c 3)) 1 6 = True :=
  implies (writtenAs (Nat.digits (writeTimes 2 c 3)) 3 2) (writtenAs (Nat.digits (writeTimes 2 c 3)) 1 6)
    (allRangeElim sixCheck 90 10 sixChecked c h1 h2) h

-- The same for 10 digits: a 5-digit block twice and a 2-digit block five times.
def tenCheck (c: Nat): Bool :=
  Bool.not (writtenAs (Nat.digits (writeTimes 2 c 5)) 5 2) || writtenAs (Nat.digits (writeTimes 2 c 5)) 1 10

theorem tenChecked: List.all tenCheck (List.rangeFrom 90 10) = True := rfl

theorem tenFromTwoAndFive (c: Nat) (h1: 10 <= c) (h2: c < 100) (h: writtenAs (Nat.digits (writeTimes 2 c 5)) 5 2 = True):
    writtenAs (Nat.digits (writeTimes 2 c 5)) 1 10 = True :=
  implies (writtenAs (Nat.digits (writeTimes 2 c 5)) 5 2) (writtenAs (Nat.digits (writeTimes 2 c 5)) 1 10)
    (allRangeElim tenCheck 90 10 tenChecked c h1 h2) h

-- (3) The digit-list facts behind `Range.repeatedTwice`, for n copies
-- instead of 2 (the twice* lemmas of Aoc.Common generalised).

-- One more copy goes on the end.
theorem concatRepSnoc (p: List Nat): (n: Nat) -> List.concat (List.replicate (Succ n) p) = List.append (List.concat (List.replicate n p)) p
  | Zero   => List.appendNil p
  | Succ n =>
    calc List.append p (List.concat (List.replicate (Succ n) p))
      _ = List.append p (List.append (List.concat (List.replicate n p)) p) := Eq.cong (List.append p) (concatRepSnoc p n)
      _ = List.append (List.append p (List.concat (List.replicate n p))) p := Eq.sym (List.appendAssoc p (List.concat (List.replicate n p)) p)

-- The digits `p` written n times make `fromDigits p` written n times.
theorem fromDigitsRep (p: List Nat): (n: Nat) -> Nat.fromDigits (List.concat (List.replicate n p)) = writeTimes (List.length p) (Nat.fromDigits p) n
  | Zero   => rfl
  | Succ n =>
    calc Nat.fromDigits (List.concat (List.replicate (Succ n) p))
      _ = Nat.fromDigits (List.append (List.concat (List.replicate n p)) p) := Eq.cong Nat.fromDigits (concatRepSnoc p n)
      _ = Nat.fromDigits (List.concat (List.replicate n p)) * Nat.pow 10 (List.length p) + Nat.fromDigits p := Nat.fromDigitsAppend (List.concat (List.replicate n p)) p
      _ = writeTimes (List.length p) (Nat.fromDigits p) n * Nat.pow 10 (List.length p) + Nat.fromDigits p := Eq.cong (\t => t * Nat.pow 10 (List.length p) + Nat.fromDigits p) (fromDigitsRep p n)

theorem repAppend (x: Nat) (k: Nat) (n: Nat) (hq: writtenAs (Nat.digits x) k n = True):
    List.concat (List.replicate n (List.take k (Nat.digits x))) = Nat.digits x :=
  Decidable.toBoolSound (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate n (List.take k (Nat.digits x)))) (Nat.digits x)) hq

-- With two or more copies the block is k digits long (it can't be all of x).
theorem repBlockLength (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True): List.length (List.take k (Nat.digits x)) = k :=
  Bool.inspect (Nat.leq k (List.length (Nat.digits x))) (\u => List.length (List.take k (Nat.digits x)) = k)
    (\t => List.lengthTake k (Nat.digits x) t)
    (\f => Void.exfalso (Nat.lessIrrefl (List.length (Nat.digits x))
      (calc Succ (List.length (Nat.digits x))
        _ <= List.length (Nat.digits x) + List.length (Nat.digits x) := Nat.leCongLeft (List.length (Nat.digits x) + 1) (Succ (List.length (Nat.digits x))) (List.length (Nat.digits x) + List.length (Nat.digits x)) (Nat.addOne (List.length (Nat.digits x))) (Nat.leAddCong (List.length (Nat.digits x)) 1 (List.length (Nat.digits x)) (Nat.digitsNonEmpty x))
        _ <= List.length (Nat.digits x) + (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) := Nat.leAddCong (List.length (Nat.digits x)) (List.length (Nat.digits x)) (List.length (Nat.digits x) + List.length (List.concat (List.replicate m (Nat.digits x)))) (Nat.leAddRight (List.length (Nat.digits x)) (List.length (List.concat (List.replicate m (Nat.digits x)))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (Nat.digits x))) := Eq.sym (Eq.trans (List.lengthAppend (Nat.digits x) (List.append (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))) (Eq.cong (\t => List.length (Nat.digits x) + t) (List.lengthAppend (Nat.digits x) (List.concat (List.replicate m (Nat.digits x))))))
        _ = List.length (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.cong (\l => List.length (List.concat (List.replicate (Succ (Succ m)) l))) (Eq.sym (List.takeAll k (Nat.digits x) (Nat.lessLe (List.length (Nat.digits x)) k (Nat.leqFalse k (List.length (Nat.digits x)) f))))
        _ = List.length (Nat.digits x) := Eq.cong List.length (repAppend x k (Succ (Succ m)) hq))))

-- x is its first k digits written n times.
theorem repValue (x: Nat) (k: Nat) (m: Nat) (hq: writtenAs (Nat.digits x) k (Succ (Succ m)) = True):
    writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m)) = x :=
  calc writeTimes k (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m))
    _ = writeTimes (List.length (List.take k (Nat.digits x))) (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m)) := Eq.cong (\t => writeTimes t (Nat.fromDigits (List.take k (Nat.digits x))) (Succ (Succ m))) (Eq.sym (repBlockLength x k m hq))
    _ = Nat.fromDigits (List.concat (List.replicate (Succ (Succ m)) (List.take k (Nat.digits x)))) := Eq.sym (fromDigitsRep (List.take k (Nat.digits x)) (Succ (Succ m)))
    _ = Nat.fromDigits (Nat.digits x) := Eq.cong Nat.fromDigits (repAppend x k (Succ (Succ m)) hq)
    _ = x := Nat.fromDigitsDigits x

-- The other way: a block of k digits (no leading 0) written n >= 1 times
-- has those digits n times.
theorem writeTimesPos (k: Nat) (b: Nat) (hb: 1 <= b) (n: Nat): 1 <= writeTimes k b (Succ n) :=
  Nat.leTrans 1 b (writeTimes k b n * Nat.pow 10 k + b) hb (Nat.leAddLeft (writeTimes k b n * Nat.pow 10 k) b)

theorem digitsRep (b: Nat) (hb: 1 <= b): (n: Nat) ->
    Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n)) = List.concat (List.replicate (Succ n) (Nat.digits b))
  | Zero   => Eq.sym (List.appendNil (Nat.digits b))
  | Succ n =>
    calc Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + b)
      _ = Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + Nat.fromDigits (Nat.digits b)) := Eq.cong (\t => Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n) * Nat.pow 10 (List.length (Nat.digits b)) + t)) (Eq.sym (Nat.fromDigitsDigits b))
      _ = List.append (Nat.digits (writeTimes (List.length (Nat.digits b)) b (Succ n))) (Nat.digits b) := Nat.digitsShift (Nat.digits b) (writeTimes (List.length (Nat.digits b)) b (Succ n)) (writeTimesPos (List.length (Nat.digits b)) b hb n) (Nat.digitsDigits b)
      _ = List.append (List.concat (List.replicate (Succ n) (Nat.digits b))) (Nat.digits b) := Eq.cong (\l => List.append l (Nat.digits b)) (digitsRep b hb n)
      _ = List.concat (List.replicate (Succ (Succ n)) (Nat.digits b)) := Eq.sym (concatRepSnoc (Nat.digits b) (Succ n))

theorem writtenRepOf (p: List Nat) (k: Nat) (hk: List.length p = k) (n: Nat): writtenAs (List.concat (List.replicate (Succ n) p)) k (Succ n) = True :=
  Decidable.toBoolOf (List.decEq (\a b => Nat.decEq a b) (List.concat (List.replicate (Succ n) (List.take k (List.concat (List.replicate (Succ n) p))))) (List.concat (List.replicate (Succ n) p)))
    (Eq.cong (\q => List.concat (List.replicate (Succ n) q)) (Eq.trans (Eq.cong (\t => List.take t (List.append p (List.concat (List.replicate n p)))) (Eq.sym hk)) (List.takeAppend p (List.concat (List.replicate n p)))))

theorem repDigits (j: Nat) (b: Nat) (h1: Nat.pow 10 j <= b) (h2: b < Nat.pow 10 (Succ j)) (n: Nat):
    writtenAs (Nat.digits (writeTimes (Succ j) b (Succ n))) (Succ j) (Succ n) = True :=
  J (\l q => writtenAs l (Succ j) (Succ n) = True) (writtenRepOf (Nat.digits b) (Succ j) (Nat.digitsLength j b h1 h2) n)
    (Eq.sym
      (Eq.trans (Eq.cong (\t => Nat.digits (writeTimes t b (Succ n))) (Eq.sym (Nat.digitsLength j b h1 h2)))
        (digitsRep b (Nat.leTrans 1 (Nat.pow 10 j) b (Nat.powSuccPos 9 j) h1) n)))

-- (4) Keeping the Int sum as "plus part minus minus part": a running total
-- `p - q`, with each weight 1, 0 or -1 adding to one side.
theorem plusStep (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.mul (OfNat 1) (Nat.toInt r)) = Int.subNatNat (p + r) q :=
  Eq.trans (Eq.cong (\t => Int.add (Int.subNatNat p q) (OfNat t)) (Nat.addZero r)) (Int.subNatNatAddOfNat r p q)

theorem zeroStep (p: Nat) (q: Nat) (r: Nat): Int.add (Int.subNatNat p q) (Int.mul (OfNat 0) (Nat.toInt r)) = Int.subNatNat p q :=
  Int.addZero (Int.subNatNat p q)

theorem minusStep (p: Nat) (q: Nat): (r: Nat) -> Int.add (Int.subNatNat p q) (Int.mul (NegSucc 0) (Nat.toInt r)) = Int.subNatNat p (q + r)
  | Zero   => Eq.trans (Int.addZero (Int.subNatNat p q)) (Eq.cong (Int.subNatNat p) (Eq.sym (Nat.addZero q)))
  | Succ r =>
    calc Int.add (Int.subNatNat p q) (NegSucc (r + 0))
      _ = Int.subNatNat p (Succ (q + (r + 0))) := Int.subNatNatAddNegSucc (r + 0) p q
      _ = Int.subNatNat p (q + Succ r) := Eq.cong (\t => Int.subNatNat p t) (Eq.trans (Eq.cong (\t => Succ (q + t)) (Nat.addZero r)) (Eq.sym (Nat.addSucc q r)))

-- At the end the minus part is part of the plus part.
theorem finish (s: Nat) (q: Nat): Int.toNat (Int.subNatNat (s + q) q) = s :=
  Eq.trans (Eq.cong (\t => Int.toNat (Int.subNatNatFrom (s + q) q t)) (Nat.subEqZero q (s + q) (Nat.leAddLeft s q))) (Nat.addSub s q)

-- (5) One id with 6 digits: with c2, c3, c6 saying its digits are a block
-- written 2, 3, 6 times, the weights (+1, +1, -1) count it once if any
-- holds. Here as "plus part = spec + minus part", in Nat.
theorem sixCombine (x: Nat): (a: Bool) -> (b: Bool) -> (c: Bool) -> (c = True -> a = True) -> (c = True -> b = True) -> (a = True -> b = True -> c = True) ->
    Nat.keepIf x a + Nat.keepIf x b = Nat.keepIf x (a || (b || c)) + Nat.keepIf x c
  | True,  True,  True,  ca, cb, abc => rfl
  | True,  True,  False, ca, cb, abc => Void.exfalso (Bool.falseNotTrue (abc rfl rfl))
  | True,  False, True,  ca, cb, abc => Void.exfalso (Bool.falseNotTrue (cb rfl))
  | True,  False, False, ca, cb, abc => rfl
  | False, True,  True,  ca, cb, abc => Void.exfalso (Bool.falseNotTrue (ca rfl))
  | False, True,  False, ca, cb, abc => Eq.sym (Nat.addZero x)
  | False, False, True,  ca, cb, abc => Void.exfalso (Bool.falseNotTrue (ca rfl))
  | False, False, False, ca, cb, abc => rfl

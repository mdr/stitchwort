-- Advent of Code 2025, day 2: product ids. An id is invalid when its decimal
-- digits are some block written twice (part 1) or two or more times (part 2).
-- Sum the invalid ids that lie in any of the given ranges.
--
--   $ stitchwort run aoc/day02.sw < aoc/inputs/day02.txt
--
-- The puzzle input is not in git (aoc/inputs/ is ignored).
--
-- Rather than test every id, add up the invalid ones arithmetically. The
-- ids made of a k-digit block written n times are base * m for the k-digit
-- bases, where m = 1 + 10^k + 10^2k + ... (12 written 3 times is
-- 12 * 10101). Those bases form an interval, so their sum is an arithmetic
-- series. Part 2 must not count 111111 three times (1 six times, 11 three
-- times, 111 twice): by inclusion-exclusion over n, the ids with some proper
-- period are the sum over n of -mu(n) times the ids with n blocks, where mu
-- is the Moebius function.

def main () : {IO} () :=
  let ranges := parseRanges (IO.readAll ())
  print "Part 1: ${solvePart1 ranges}"
  print "Part 2: ${solvePart2 ranges}"

def solvePart1 (ranges : List Range) : Nat := total twice ranges

def solvePart2 (ranges : List Range) : Nat := total weight ranges

def total (w : Nat -> Int) (ranges : List Range) : Nat :=
  ranges
    |> .map (.invalid w)
    |> .sumInt
    |> .toNat

-- A range of ids, both ends included.
type Range = { lo : Nat, hi : Nat }

def Range.parse (t : Text) : Maybe Range :=
  match (t.split '-').map Text.toNat with
    | [Just lo, Just hi] => Just { lo, hi }
    | _                  => Nothing

def parseRanges (t : Text) : List Range :=
  t.trim.split ',' |> .mapMaybe Range.parse

-- The sum of the ids in the range that are a k-digit block written n times.
-- m is the multiplier: 12 written 3 times is 12 * 10101, and 10101 is
-- 1 + 10^2 + 10^4.
def Range.repeated (r : Range) (k : Nat) (n : Nat) : Nat :=
  let m := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))
  if m != 0 then
    let lo := Nat.max (Nat.pow 10 (k - 1)) ((r.lo + m - 1) / m)
    let hi := Nat.min (Nat.pow 10 k - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

-- Minus the Moebius function, for the repeat counts 2 to 10.
def weight : Nat -> Int
  | 2  => 1
  | 3  => 1
  | 5  => 1
  | 6  => -1
  | 7  => 1
  | 10 => -1
  | _  => 0

-- Part 1 only wants a block written exactly twice.
def twice (n : Nat) : Int := if n == 2 then 1 else 0

-- The invalid ids in the range under a weighting of the repeat counts: every
-- block size k and repeat count n that fit in the digits of `hi` (n is at
-- most 10, the most the weights cover).
def Range.invalid (w : Nat -> Int) (r : Range) : Int :=
  let size := (Nat.digits r.hi).length
  -- `size` is a parameter (not the `let`'s, which `terms` would know is
  -- the digit count) so the proofs below state their lemmas for any size.
  def terms (size : Nat) (k : Nat) : List Int :=
    List.rangeFrom 9 2
      |> .filter (\n => k * n <= size)
      |> .map (\n => w n * (r.repeated k n).toInt)
  List.rangeFrom size 1
    |> .concatMap (terms size)
    |> .sumInt

-- Examples -----------------------------------------------------------------

def range (lo hi : Nat) : Range := { lo, hi }

def example : Text := "11-22,95-115,998-1012,1188511880-1188511890,222220-222224,1698522-1698528,446443-446449,38593856-38593862,565653-565659,824824821-824824827,2121212118-2121212124"

test "example" := (solvePart1 (parseRanges example), solvePart2 (parseRanges example)) == (1227775554, 4174379265)
test "parse" := parseRanges "4-14,1490-3407\n" == [range 4 14, range 1490 3407]
test "parse junk" := Range.parse "4-x" == Nothing
test "12 written 3 times" := (range 0 1000000).repeated 2 3 == 10101 * ((10 + 99) * 90 / 2)
test "single range" := (range 11 22).invalid twice == 33
test "no double counting" := (range 111110 111112).invalid weight == 111111
test "period three" := (range 998 1012).invalid weight == 999 + 1010
test "empty overlap" := (range 12 21).invalid weight == 0

test "twice is weight at 2" := twice 2 == weight 2

-- Cross-check against brute force ---------------------------------------
--
-- Part 2's inclusion-exclusion isn't proved; instead it's compared with the
-- obvious method on many small ranges: look at every id's digits.

-- The digits are some block of k digits written n times.
def writtenAs (ds : List Nat) (k : Nat) (n : Nat) : Bool := List.concat (List.replicate n (List.take k ds)) == ds

-- Part 1: written twice; part 2: written two or more times.
def doubled (x : Nat) : Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => writtenAs ds k 2)

def repeats (x : Nat) : Bool :=
  let ds := Nat.digits x
  List.rangeFrom ds.length 1 |> .any (\k => List.rangeFrom ds.length 2 |> .any (\n => writtenAs ds k n))

def bruteSum (invalid : Nat -> Bool) (r : Range) : Nat :=
  List.rangeFrom (r.hi + 1 - r.lo) r.lo |> .filter invalid |> .sum

def agrees (r : Range) : Bool :=
  r.invalid twice == (bruteSum doubled r).toInt && r.invalid weight == (bruteSum repeats r).toInt

-- Ranges of 40 ids starting every 13 up to 2000, and some that cross into
-- more digits.
def checkRanges : List Range :=
  (List.rangeFrom 154 0 |> .map (\i => range (13 * i) (13 * i + 39)))
    ++ [range 95 115, range 990 1010, range 9990 10010, range 99990 100010, range 111100 111200, range 999990 1000010]

test "brute force agrees" := checkRanges.all agrees

-- Proofs -------------------------------------------------------------------
--
-- (a) `repeatedCorrect`: `r.repeated k n` equals `r.repeatedSpec k n`, the
--     brute-force sum below, for every range, block length and repeat count.
-- (b) `part1Correct`: the printed part 1 is `part1Spec`, the brute-force sum
--     over every range and block length of the blocks written twice.
-- Part 2's inclusion-exclusion isn't proved (see the cross-check above).
--
-- The outline of (a): writing a block `b` n times gives `b * m`
-- (`writeTimesMul`); `lo <= b * m <= hi` exactly when `b` is between
-- `lo / m` rounded up and `hi / m` rounded down (`roundUpLe` and friends);
-- so the ids in the range are `m` times an interval of blocks (`window`),
-- whose sum is Gauss's formula (`List.gaussSum`).

-- The specification. `writeTimes k b n` is the block `b` written `n` times:
-- each copy shifts the ones before it left by `k` digits (`b` has `k` digits).
def writeTimes (k : Nat) (b : Nat) : Nat -> Nat
  | Zero   => 0
  | Succ n => writeTimes k b n * Nat.pow 10 k + b

-- Brute force: write every k-digit block n times, keep the ids inside the
-- range, and add them up. It walks the blocks rather than the ids, but it
-- counts the same ids: each id that is a block written n times is so for just
-- one block (its first k digits).
def Range.repeatedSpec (r : Range) (k : Nat) (n : Nat) : Nat :=
  List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))
    |> .map (\b => writeTimes k b n)
    |> .filter (\x => r.lo <= x && x <= r.hi)
    |> .sum

-- `Range.repeated` with its parts as parameters: the multiplier `m`, the
-- smallest block `low` and the first number too long to be a block `p`.
def multiplier (k : Nat) (n : Nat) : Nat := List.range n |> .sumBy (\i => Nat.pow 10 (k * i))

def blocksAt (r : Range) (low : Nat) (p : Nat) (m : Nat) : Nat :=
  if m != 0 then
    let lo := Nat.max low ((r.lo + m - 1) / m)
    let hi := Nat.min (p - 1) (r.hi / m)
    if lo <= hi then m * ((lo + hi) * (hi - lo + 1) / 2) else 0
  else 0

theorem repeatedAt (r : Range) (k : Nat) (n : Nat) : r.repeated k n = blocksAt r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (multiplier k n) := rfl

-- The multiplier: writing `b` n times is `b * multiplier k n`.
theorem multiplierSucc (k : Nat) (n : Nat) : multiplier k (Succ n) = 1 + Nat.pow 10 k * multiplier k n :=
  Eq.trans (List.sumByCons (\i => Nat.pow 10 (k * i)) 0 (List.rangeFrom n 1))
    (Eq.trans (Eq.cong (\t => Nat.pow 10 t + List.sumBy (\i => Nat.pow 10 (k * i)) (List.rangeFrom n 1)) (Nat.mulZero k))
      (Eq.cong (\t => 1 + t)
        (Eq.trans (List.sumByRangeShift (\i => Nat.pow 10 (k * i)) n 0)
          (Eq.trans (List.sumByCongr (\i => Nat.pow 10 (k * Succ i)) (\i => Nat.pow 10 k * Nat.pow 10 (k * i))
              (\i => Eq.trans (Eq.cong (\t => Nat.pow 10 t) (Nat.mulSucc k i)) (Nat.powAdd 10 k (k * i))) (List.range n))
            (List.sumByMulLeft (Nat.pow 10 k) (\i => Nat.pow 10 (k * i)) (List.range n))))))

theorem writeTimesMul (k : Nat) (b : Nat) : (n : Nat) -> writeTimes k b n = b * multiplier k n
  | Zero   => Eq.sym (Nat.mulZero b)
  | Succ n =>
    Eq.trans (Eq.cong (\t => t * Nat.pow 10 k + b) (writeTimesMul k b n))
      (Eq.trans (Eq.cong (\t => t + b) (Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)))
        (Eq.trans (Eq.cong (\t => b * t + b) (Nat.mulComm (multiplier k n) (Nat.pow 10 k)))
          (Eq.trans (Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b)
            (Eq.trans (Eq.cong (\t => t + b * (Nat.pow 10 k * multiplier k n)) (Eq.sym (Nat.mulOne b)))
              (Eq.trans (Eq.sym (Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)))
                (Eq.cong (\t => b * t) (Eq.sym (multiplierSucc k n))))))))

-- The ids `b * d` for `b` from `s` to `s + c - 1` that lie in `lo..hi`, added up.
def windowSum (lo : Nat) (hi : Nat) (d : Nat) (c : Nat) (s : Nat) : Nat :=
  List.sum (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * d) (List.rangeFrom c s)))

-- `x + (x + 1) + ... + (y - 1)`
def span (x : Nat) (y : Nat) : Nat := List.sum (List.rangeFrom (y - x) x)

theorem specWindow (r : Range) (k : Nat) (n : Nat) :
    r.repeatedSpec k n = windowSum r.lo r.hi (multiplier k n) (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1)) :=
  Eq.cong (\xs => List.sum (List.filter (\x => r.lo <= x && x <= r.hi) xs))
    (List.mapCongr (\b => writeTimes k b n) (\b => b * multiplier k n) (\b => writeTimesMul k b n)
      (List.rangeFrom (Nat.pow 10 k - Nat.pow 10 (k - 1)) (Nat.pow 10 (k - 1))))

theorem inRangeYes (lo : Nat) (hi : Nat) (x : Nat) (h1 : lo <= x) (h2 : x <= hi) : (lo <= x && x <= hi) = True :=
  J (\c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (\u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (\u => False) = True)
    (J (\c q => Decidable.toBool (Bool.decTrue c) = True) rfl (Eq.sym h2)) (Eq.sym h1)

theorem inRangeBelow (lo : Nat) (hi : Nat) (x : Nat) (h : Nat.leq lo x = False) : (lo <= x && x <= hi) = False :=
  J (\c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (\u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (\u => False) = False) rfl (Eq.sym h)

theorem inRangeAbove (lo : Nat) (hi : Nat) (x : Nat) (h1 : lo <= x) (h2 : Nat.leq x hi = False) : (lo <= x && x <= hi) = False :=
  J (\c q => Bool.ifThenElse (Decidable.toBool (Bool.decTrue c)) (\u => Decidable.toBool (Bool.decTrue (Nat.leq x hi))) (\u => False) = False)
    (J (\c q => Decidable.toBool (Bool.decTrue c) = False) rfl (Eq.sym h2)) (Eq.sym h1)

-- With a multiplier of 0 every id is 0.
theorem windowZero (lo : Nat) (hi : Nat) : (c : Nat) -> (s : Nat) -> windowSum lo hi 0 c s = 0
  | Zero,   s => rfl
  | Succ c, s =>
    Bool.inspect (lo <= s * 0 && s * 0 <= hi) (\u => windowSum lo hi 0 (Succ c) s = 0)
      (\h => Eq.trans (Eq.cong List.sum (List.filterKeep (\x => lo <= x && x <= hi) (s * 0) (List.map (\b => b * 0) (List.rangeFrom c (Succ s))) h))
        (Eq.trans (List.sumCons (s * 0) (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * 0) (List.rangeFrom c (Succ s)))))
          (Eq.trans (Eq.cong (\t => t + windowSum lo hi 0 c (Succ s)) (Nat.mulZero s)) (windowZero lo hi c (Succ s)))))
      (\h => Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * 0) (List.map (\b => b * 0) (List.rangeFrom c (Succ s))) h))
        (windowZero lo hi c (Succ s)))

theorem spanEmpty (x : Nat) (y : Nat) (h : y <= x) : span x y = 0 := Eq.cong (\t => List.sum (List.rangeFrom t x)) (Nat.subEqZero y x h)

theorem spanStep (s : Nat) (y : Nat) (h : Succ s <= y) : span s y = s + span (Succ s) y :=
  Eq.trans (Eq.cong (\t => List.sum (List.rangeFrom t s)) (Nat.subSuccRight s y h)) (List.sumCons s (List.rangeFrom (y - Succ s) (Succ s)))

-- One step of `window`, for each place `s` can be: below `bLo`, in `bLo..bHi`, above `bHi`.
theorem windowBelow (lo : Nat) (hi : Nat) (d : Nat) (bLo : Nat) (bHi : Nat) (c : Nat) (s : Nat)
    (no : Nat.leq lo (s * d) = False) (hs : Succ s <= bLo)
    (ih : windowSum lo hi d c (Succ s) = d * span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))) :
    windowSum lo hi d (Succ c) s = d * span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (inRangeBelow lo hi (s * d) no)))
    (Eq.trans ih
      (Eq.trans (Eq.cong (\t => d * span t (Nat.min (Succ s + c) (Succ bHi))) (Nat.maxRight (Succ s) bLo hs))
        (Eq.sym (Eq.trans (Eq.cong (\t => d * span t (Nat.min (s + Succ c) (Succ bHi))) (Nat.maxRight s bLo (Nat.lessLe s bLo hs)))
          (Eq.cong (\t => d * span bLo (Nat.min t (Succ bHi))) (Nat.addSucc s c))))))

theorem windowIn (lo : Nat) (hi : Nat) (d : Nat) (bLo : Nat) (bHi : Nat) (c : Nat) (s : Nat)
    (yes : (lo <= s * d && s * d <= hi) = True) (hA : bLo <= s) (hB : s <= bHi)
    (ih : windowSum lo hi d c (Succ s) = d * span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))) :
    windowSum lo hi d (Succ c) s = d * span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterKeep (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) yes))
    (Eq.trans (List.sumCons (s * d) (List.filter (\x => lo <= x && x <= hi) (List.map (\b => b * d) (List.rangeFrom c (Succ s)))))
      (Eq.trans (Eq.cong (\t => s * d + t) ih)
        (Eq.trans (Eq.cong (\t => s * d + d * span t (Nat.min (Succ s + c) (Succ bHi))) (Nat.maxLeft (Succ s) bLo (Nat.leTrans bLo s (Succ s) hA (Nat.leSucc s))))
          (Eq.trans (Eq.cong (\t => t + d * span (Succ s) (Nat.min (Succ s + c) (Succ bHi))) (Nat.mulComm s d))
            (Eq.sym
              (Eq.trans (Eq.cong (\t => d * span t (Nat.min (s + Succ c) (Succ bHi))) (Nat.maxLeft s bLo hA))
                (Eq.trans (Eq.cong (\t => d * span s (Nat.min t (Succ bHi))) (Nat.addSucc s c))
                  (Eq.trans (Eq.cong (\t => d * t) (spanStep s (Nat.min (Succ s + c) (Succ bHi)) (Nat.leMin (Succ s) (Succ s + c) (Succ bHi) (Nat.leAddRight s c) hB)))
                    (Nat.mulDistribLeft d s (span (Succ s) (Nat.min (Succ s + c) (Succ bHi))))))))))))

theorem windowAbove (lo : Nat) (hi : Nat) (d : Nat) (bLo : Nat) (bHi : Nat) (c : Nat) (s : Nat)
    (low : lo <= s * d) (no : Nat.leq (s * d) hi = False) (hs : Succ bHi <= s)
    (ih : windowSum lo hi d c (Succ s) = d * span (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))) :
    windowSum lo hi d (Succ c) s = d * span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)) :=
  Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (s * d) (List.map (\b => b * d) (List.rangeFrom c (Succ s))) (inRangeAbove lo hi (s * d) low no)))
    (Eq.trans ih
      (Eq.trans (Eq.cong (\t => d * t)
          (spanEmpty (Nat.max (Succ s) bLo) (Nat.min (Succ s + c) (Succ bHi))
            (Nat.leTrans (Nat.min (Succ s + c) (Succ bHi)) (Succ s) (Nat.max (Succ s) bLo)
              (Nat.leTrans (Nat.min (Succ s + c) (Succ bHi)) (Succ bHi) (Succ s) (Nat.minLeRight (Succ s + c) (Succ bHi)) (Nat.leTrans (Succ bHi) s (Succ s) hs (Nat.leSucc s)))
              (Nat.leMaxLeft (Succ s) bLo))))
        (Eq.trans (Nat.mulZero d)
          (Eq.sym (Eq.trans (Eq.cong (\t => d * t)
              (spanEmpty (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi))
                (Nat.leTrans (Nat.min (s + Succ c) (Succ bHi)) s (Nat.max s bLo)
                  (Nat.leTrans (Nat.min (s + Succ c) (Succ bHi)) (Succ bHi) s (Nat.minLeRight (s + Succ c) (Succ bHi)) hs)
                  (Nat.leMaxLeft s bLo))))
            (Nat.mulZero d))))))

-- The heart of it: if `lo <= b * d` exactly when `bLo <= b`, and `b * d <= hi`
-- exactly when `b <= bHi`, then the ids `b * d` in `lo..hi` for `b` in a run of
-- `c` numbers from `s` are `d` times the sum of the run cut down to `bLo..bHi`.
theorem window (lo : Nat) (hi : Nat) (d : Nat) (bLo : Nat) (bHi : Nat)
    (yesA : (b : Nat) -> bLo <= b -> lo <= b * d)
    (noA : (b : Nat) -> Nat.leq bLo b = False -> Nat.leq lo (b * d) = False)
    (yesB : (b : Nat) -> b <= bHi -> b * d <= hi)
    (noB : (b : Nat) -> Nat.leq b bHi = False -> Nat.leq (b * d) hi = False) :
    (c : Nat) -> (s : Nat) -> windowSum lo hi d c s = d * span (Nat.max s bLo) (Nat.min (s + c) (Succ bHi))
  | Zero,   s =>
    Eq.sym (Eq.trans (Eq.cong (\t => d * t)
        (spanEmpty (Nat.max s bLo) (Nat.min (s + 0) (Succ bHi))
          (Nat.leTrans (Nat.min (s + 0) (Succ bHi)) s (Nat.max s bLo)
            (Nat.leCongRight (Nat.min (s + 0) (Succ bHi)) (s + 0) s (Nat.addZero s) (Nat.minLeLeft (s + 0) (Succ bHi)))
            (Nat.leMaxLeft s bLo))))
      (Nat.mulZero d))
  | Succ c, s =>
    Bool.inspect (Nat.leq bLo s) (\u => windowSum lo hi d (Succ c) s = d * span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)))
      (\hA => Bool.inspect (Nat.leq s bHi) (\u => windowSum lo hi d (Succ c) s = d * span (Nat.max s bLo) (Nat.min (s + Succ c) (Succ bHi)))
        (\hB => windowIn lo hi d bLo bHi c s (inRangeYes lo hi (s * d) (yesA s hA) (yesB s hB)) hA hB (window lo hi d bLo bHi yesA noA yesB noB c (Succ s)))
        (\nB => windowAbove lo hi d bLo bHi c s (yesA s hA) (noB s nB) (Nat.leqFalse s bHi nB) (window lo hi d bLo bHi yesA noA yesB noB c (Succ s))))
      (\nA => windowBelow lo hi d bLo bHi c s (noA s nA) (Nat.leqFalse bLo s nA) (window lo hi d bLo bHi yesA noA yesB noB c (Succ s)))

-- Rounding up and down: with `d = Succ m`, `lo <= b * d` exactly when
-- `(lo + d - 1) / d <= b`, and `b * d <= hi` exactly when `b <= hi / d`.
theorem roundUpArg (lo : Nat) (m : Nat) : lo + Succ m - 1 = lo + m := Eq.cong (\t => t - 1) (Nat.addSucc lo m)

theorem roundUpLe (lo : Nat) (m : Nat) (b : Nat) (h : lo <= b * Succ m) : (lo + Succ m - 1) / Succ m <= b :=
  Nat.leCongLeft ((lo + m) / Succ m) ((lo + Succ m - 1) / Succ m) b (Eq.cong (\t => t / Succ m) (Eq.sym (roundUpArg lo m)))
    (Nat.divLeOfLtMul (lo + m) b (Succ m) (Nat.leCongLeft (m + lo) (lo + m) (m + b * Succ m) (Nat.addComm m lo) (Nat.leAddCong m lo (b * Succ m) h)))

theorem roundUpGe (lo : Nat) (m : Nat) (b : Nat) (h : (lo + Succ m - 1) / Succ m <= b) : lo <= b * Succ m :=
  Nat.leTrans lo (((lo + m) / Succ m) * Succ m) (b * Succ m)
    (Nat.leAddCancel m lo (((lo + m) / Succ m) * Succ m)
      (Nat.leCongLeft (lo + m) (m + lo) (m + ((lo + m) / Succ m) * Succ m) (Nat.addComm lo m)
        (Nat.divFuelBound (lo + m) (lo + m) (Succ m) (Nat.succNotZero m) (Nat.leRefl (lo + m)))))
    (Nat.leMulRight ((lo + m) / Succ m) b (Succ m) (Nat.leCongLeft ((lo + Succ m - 1) / Succ m) ((lo + m) / Succ m) b (Eq.cong (\t => t / Succ m) (roundUpArg lo m)) h))

theorem roundUpNo (lo : Nat) (m : Nat) (b : Nat) (h : Nat.leq ((lo + Succ m - 1) / Succ m) b = False) : Nat.leq lo (b * Succ m) = False :=
  Bool.inspect (Nat.leq lo (b * Succ m)) (\c => c = False)
    (\t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (roundUpLe lo m b t))))
    (\f => rfl)

theorem roundDownNo (hi : Nat) (m : Nat) (b : Nat) (h : Nat.leq b (hi / Succ m) = False) : Nat.leq (b * Succ m) hi = False :=
  Bool.inspect (Nat.leq (b * Succ m) hi) (\c => c = False)
    (\t => Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym h) (Nat.leDivOfMulLe b hi (Succ m) t))))
    (\f => rfl)

-- The closed form is the sum of `lo..hi`.
theorem gaussSpan (d : Nat) (lo : Nat) (hi : Nat) (h : lo <= hi) : d * ((lo + hi) * (hi - lo + 1) / 2) = d * span lo (Succ hi) :=
  Eq.trans
    (Eq.cong (\t => d * (t / 2))
      (Eq.trans (Eq.cong (\t => (lo + t) * (hi - lo + 1)) (Eq.sym (Nat.addSubCancel lo hi h)))
        (Eq.trans (Eq.cong (\t => (lo + (lo + (hi - lo))) * t) (Nat.addOne (hi - lo)))
          (Eq.trans (Nat.mulComm (lo + (lo + (hi - lo))) (Succ (hi - lo))) (Eq.sym (List.gaussSum (hi - lo) lo))))))
    (Eq.trans (Eq.cong (\t => d * t) (Nat.halfDouble (List.sum (List.rangeFrom (Succ (hi - lo)) lo))))
      (Eq.sym (Eq.cong (\t => d * List.sum (List.rangeFrom t lo)) (Nat.subSuccRight lo (Succ hi) h))))

-- The `if` at the end of `blocksAt`, after its `let`s. A proof by cases
-- replaces its condition `Nat.leq lo hi` by a variable `c`; `if IsTrue c`
-- decides with `Bool.decTrue c`, as `if lo <= hi` does (`if c = True` would
-- use `Bool.decEq`, a different term).
def IsTrue (c : Bool) : Prop := c = True

def decIsTrue (c : Bool) : Decidable (IsTrue c) := Bool.decTrue c

theorem gaussPick (d : Nat) (lo : Nat) (hi : Nat) :
    (if lo <= hi then d * ((lo + hi) * (hi - lo + 1) / 2) else 0) = d * span lo (Succ hi) :=
  Bool.inspect (Nat.leq lo hi)
    (\c => (if IsTrue c then d * ((lo + hi) * (hi - lo + 1) / 2) else 0) = d * span lo (Succ hi))
    (\h => gaussSpan d lo hi h)
    (\h => Eq.sym (Eq.trans (Eq.cong (\t => d * t) (spanEmpty lo (Succ hi) (Nat.leqFalse lo hi h))) (Nat.mulZero d)))

theorem blocksWindow (r : Range) (low : Nat) : (p : Nat) -> 0 < p -> low <= p -> (m : Nat) ->
    blocksAt r low p m = windowSum r.lo r.hi m (p - low) low
  | Zero,   hp, hl, m      => Void.exfalso (Bool.falseNotTrue hp)
  | Succ p, hp, hl, Zero   => Eq.sym (windowZero r.lo r.hi (Succ p - low) low)
  | Succ p, hp, hl, Succ m =>
    Eq.trans (gaussPick (Succ m) (Nat.max low ((r.lo + Succ m - 1) / Succ m)) (Nat.min p (r.hi / Succ m)))
      (Eq.sym
        (Eq.trans
          (window r.lo r.hi (Succ m) ((r.lo + Succ m - 1) / Succ m) (r.hi / Succ m)
            (roundUpGe r.lo m) (roundUpNo r.lo m) (\b h => Nat.mulLeOfLeDiv b r.hi (Succ m) h) (roundDownNo r.hi m)
            (Succ p - low) low)
          (Eq.trans (Eq.cong (\t => Succ m * span (Nat.max low ((r.lo + Succ m - 1) / Succ m)) (Nat.min t (Succ (r.hi / Succ m)))) (Nat.addSubCancel low (Succ p) hl))
            (Eq.cong (\t => Succ m * span (Nat.max low ((r.lo + Succ m - 1) / Succ m)) t) (Nat.minSucc p (r.hi / Succ m))))))

theorem lowerLe : (k : Nat) -> Nat.pow 10 (k - 1) <= Nat.pow 10 k
  | Zero   => rfl
  | Succ k => Nat.leAddRight (Nat.pow 10 k) (9 * Nat.pow 10 k)

-- (a) The arithmetic sum is the brute-force one.
theorem repeatedCorrect (r : Range) (k : Nat) (n : Nat) : r.repeated k n = r.repeatedSpec k n :=
  Eq.trans (blocksWindow r (Nat.pow 10 (k - 1)) (Nat.pow 10 k) (Nat.powSuccPos 9 k) (lowerLe k) (multiplier k n))
    (Eq.sym (specWindow r k n))

-- Part 1 -------------------------------------------------------------------

-- Brute force for part 1: in each range, every block length up to the
-- number of digits of `hi` (a longer block makes a longer id), every block of
-- that length written twice.
def part1Spec (ranges : List Range) : Nat :=
  ranges |> .sumBy (\r => List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => r.repeatedSpec k 2))

-- `n / 10 < n` once `n` has two digits.
theorem divTenLess : (n : Nat) -> Nat.leq n 9 = False -> Succ (n / 10) <= n
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ n, h =>
    Nat.divLeOfLtMul (Succ n) n 10
      (Nat.leTrans n (n * 10) (8 + n * 10)
        (Nat.leCongRight n (n + n * 9) (n * 10) (Eq.sym (Nat.mulSucc n 9)) (Nat.leAddRight n (n * 9)))
        (Nat.leAddLeft 8 (n * 10)))

-- `n` has few enough digits: `n < 10 ^ (number of digits)`.
theorem digitsBound : (fuel : Nat) -> (n : Nat) -> (acc : List Nat) -> n < fuel ->
    Succ n * Nat.pow 10 (List.length acc) <= Nat.pow 10 (List.length (Nat.digitsFuel fuel n acc))
  | Zero,      n, acc, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ fuel, n, acc, h =>
    Bool.inspect (Nat.leq n 9)
      (\c => Succ n * Nat.pow 10 (List.length acc)
        <= Nat.pow 10 (List.length (Bool.ifThenElse c (\u => Cons n acc) (\u => Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc)))))
      (\small => Nat.leMulRight (Succ n) 10 (Nat.pow 10 (List.length acc)) small)
      (\big => Nat.leTrans (Succ n * Nat.pow 10 (List.length acc)) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc))
        (Nat.pow 10 (List.length (Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc))))
        (Nat.leMulRight (Succ n) (Succ (n / 10) * 10) (Nat.pow 10 (List.length acc)) (Nat.divFuelBound n n 10 (Nat.succNotZero 9) (Nat.leRefl n)))
        (Nat.leCongLeft (Succ (n / 10) * (10 * Nat.pow 10 (List.length acc))) ((Succ (n / 10) * 10) * Nat.pow 10 (List.length acc)) (Nat.pow 10 (List.length (Nat.digitsFuel fuel (n / 10) (Cons (n % 10) acc))))
          (Eq.sym (Nat.mulAssoc (Succ (n / 10)) 10 (Nat.pow 10 (List.length acc))))
          (digitsBound fuel (n / 10) (Cons (n % 10) acc) (Nat.leTrans (Succ (n / 10)) n fuel (divTenLess n big) h))))

theorem hiBound (hi : Nat) : hi < Nat.pow 10 (List.length (Nat.digits hi)) :=
  Nat.leCongLeft (Succ hi * 1) (Succ hi) (Nat.pow 10 (List.length (Nat.digits hi))) (Nat.mulOne (Succ hi))
    (digitsBound (Succ hi) hi Nil (Nat.leRefl hi))

theorem inRangeOver (lo : Nat) (hi : Nat) (x : Nat) (h : Nat.leq x hi = False) : (lo <= x && x <= hi) = False :=
  Bool.inspect (Nat.leq lo x) (\c => (lo <= x && x <= hi) = False) (\t => inRangeAbove lo hi x t h) (\f => inRangeBelow lo hi x f)

-- If every block from `low` on makes an id above `hi`, none is in the range.
theorem noneInRange (lo : Nat) (hi : Nat) (w : Nat -> Nat) (low : Nat) (big : (b : Nat) -> low <= b -> Nat.leq (w b) hi = False) :
    (c : Nat) -> (s : Nat) -> low <= s -> List.sum (List.filter (\x => lo <= x && x <= hi) (List.map w (List.rangeFrom c s))) = 0
  | Zero,   s, h => rfl
  | Succ c, s, h =>
    Eq.trans (Eq.cong List.sum (List.filterSkip (\x => lo <= x && x <= hi) (w s) (List.map w (List.rangeFrom c (Succ s))) (inRangeOver lo hi (w s) (big s h))))
      (noneInRange lo hi w low big c (Succ s) (Nat.leTrans low s (Succ s) h (Nat.leSucc s)))

-- A block of k digits written twice has 2k digits, too many when `hi` has fewer.
theorem tooLong (r : Range) : (k : Nat) -> Nat.leq (k * 2) (List.length (Nat.digits r.hi)) = False -> r.repeatedSpec k 2 = 0
  | Zero,   h => Void.exfalso (Bool.trueNotFalse h)
  | Succ k, h =>
    noneInRange r.lo r.hi (\b => writeTimes (Succ k) b 2) (Nat.pow 10 k)
      (\b hb => Nat.leqFalseOfLess r.hi (b * Nat.pow 10 (Succ k) + b)
        (Nat.leTrans (Succ r.hi) (Nat.pow 10 (List.length (Nat.digits r.hi))) (b * Nat.pow 10 (Succ k) + b) (hiBound r.hi)
          (Nat.leTrans (Nat.pow 10 (List.length (Nat.digits r.hi))) (Nat.pow 10 (k + Succ k)) (b * Nat.pow 10 (Succ k) + b)
            (Nat.powMono 9 (List.length (Nat.digits r.hi)) (k + Succ k)
              (Nat.leCongRight (List.length (Nat.digits r.hi)) (Succ (k * 2)) (k + Succ k)
                (Eq.trans (Eq.cong Succ (Eq.trans (Nat.mulSucc k 1) (Eq.cong (\t => k + t) (Nat.mulOne k)))) (Eq.sym (Nat.addSucc k k)))
                (Nat.leqFalse (Succ k * 2) (List.length (Nat.digits r.hi)) h)))
            (Nat.leCongLeft (Nat.pow 10 k * Nat.pow 10 (Succ k)) (Nat.pow 10 (k + Succ k)) (b * Nat.pow 10 (Succ k) + b) (Eq.sym (Nat.powAdd 10 k (Succ k)))
              (Nat.leTrans (Nat.pow 10 k * Nat.pow 10 (Succ k)) (b * Nat.pow 10 (Succ k)) (b * Nat.pow 10 (Succ k) + b)
                (Nat.leMulRight (Nat.pow 10 k) b (Nat.pow 10 (Succ k)) hb)
                (Nat.leAddRight (b * Nat.pow 10 (Succ k)) b))))))
      (Nat.pow 10 (Succ k) - Nat.pow 10 k) (Nat.pow 10 k) (Nat.leRefl (Nat.pow 10 k))

-- Repeat counts other than 2 count for nothing in part 1.
theorem laterCounts (r : Range) (k : Nat) (size : Nat) : (a : Int) -> (c : Nat) -> (s : Nat) ->
    List.foldLeft Int.add a (List.map (\n => twice n * (r.repeated k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom c (Succ (Succ (Succ s)))))) = a
  | a, Zero,   s => rfl
  | a, Succ c, s =>
    Bool.inspect (k * Succ (Succ (Succ s)) <= size)
      (\u => List.foldLeft Int.add a (List.map (\n => twice n * (r.repeated k n).toInt) (List.filter (\n => k * n <= size) (List.rangeFrom (Succ c) (Succ (Succ (Succ s)))))) = a)
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add a (List.map (\n => twice n * (r.repeated k n).toInt) xs))
          (List.filterKeep (\n => k * n <= size) (Succ (Succ (Succ s))) (List.rangeFrom c (Succ (Succ (Succ (Succ s))))) h))
        (Eq.trans (laterCounts r k size (Int.add a (Nat.toInt 0)) c (Succ s)) (Int.addZero a)))
      (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add a (List.map (\n => twice n * (r.repeated k n).toInt) xs))
          (List.filterSkip (\n => k * n <= size) (Succ (Succ (Succ s))) (List.rangeFrom c (Succ (Succ (Succ (Succ s))))) h))
        (laterCounts r k size a c (Succ s)))

-- One block length's terms: the block written twice, if it fits.
theorem termsSum (r : Range) (k : Nat) (size : Nat) (a : Nat) (fits : Nat.leq (k * 2) size = False -> r.repeatedSpec k 2 = 0) :
    List.foldLeft Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) = Nat.toInt (a + r.repeatedSpec k 2) :=
  Bool.inspect (k * 2 <= size)
    (\u => List.foldLeft Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) = Nat.toInt (a + r.repeatedSpec k 2))
    (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Nat.toInt a) (List.map (\n => twice n * (r.repeated k n).toInt) xs))
        (List.filterKeep (\n => k * n <= size) 2 (List.rangeFrom 8 3) h))
      (Eq.trans (laterCounts r k size (Int.add (Nat.toInt a) (twice 2 * (r.repeated k 2).toInt)) 8 0)
        (Eq.cong (\t => Nat.toInt (a + t)) (Eq.trans (Nat.addZero (r.repeated k 2)) (repeatedCorrect r k 2)))))
    (\h => Eq.trans (Eq.cong (\xs => List.foldLeft Int.add (Nat.toInt a) (List.map (\n => twice n * (r.repeated k n).toInt) xs))
        (List.filterSkip (\n => k * n <= size) 2 (List.rangeFrom 8 3) h))
      (Eq.trans (laterCounts r k size (Nat.toInt a) 8 0)
        (Eq.cong (\t => Nat.toInt t) (Eq.sym (Eq.trans (Eq.cong (\t => a + t) (fits (Eq.trans (Eq.sym (Bool.decTrueToBool (Nat.leq (k * 2) size))) h))) (Nat.addZero a))))))

theorem rangeTerms (r : Range) (size : Nat) (fits : (k : Nat) -> Nat.leq (k * 2) size = False -> r.repeatedSpec k 2 = 0) :
    (ks : List Nat) -> (a : Nat) ->
    List.foldLeft Int.add (Nat.toInt a) (List.concatMap (Range.invalid.terms twice r size) ks)
      = Nat.toInt (List.foldLeft (\acc k => acc + r.repeatedSpec k 2) a ks)
  | Nil,       a => rfl
  | Cons k ks, a =>
    Eq.trans (List.foldLeftAppend Int.add (Nat.toInt a) (Range.invalid.terms twice r size k) (List.concatMap (Range.invalid.terms twice r size) ks))
      (Eq.trans (Eq.cong (\z => List.foldLeft Int.add z (List.concatMap (Range.invalid.terms twice r size) ks)) (termsSum r k size a (fits k)))
        (rangeTerms r size fits ks (a + r.repeatedSpec k 2)))

theorem invalidTwice (r : Range) :
    r.invalid twice = Nat.toInt (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => r.repeatedSpec k 2)) :=
  rangeTerms r (List.length (Nat.digits r.hi)) (tooLong r) (List.rangeFrom (List.length (Nat.digits r.hi)) 1) 0

theorem totalTwice : (ranges : List Range) -> (a : Nat) ->
    List.foldLeft Int.add (Nat.toInt a) (List.map (Range.invalid twice) ranges)
      = Nat.toInt (List.foldLeft (\acc r => acc + (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => r.repeatedSpec k 2))) a ranges)
  | Nil,       a => rfl
  | Cons r rs, a =>
    Eq.trans (Eq.cong (\t => List.foldLeft Int.add (Int.add (Nat.toInt a) t) (List.map (Range.invalid twice) rs)) (invalidTwice r))
      (totalTwice rs (a + (List.rangeFrom (Nat.digits r.hi).length 1 |> .sumBy (\k => r.repeatedSpec k 2))))

-- (b) Part 1 is the brute-force sum.
theorem part1Correct (ranges : List Range) : solvePart1 ranges = part1Spec ranges :=
  Eq.cong Int.toNat (totalTwice ranges 0)

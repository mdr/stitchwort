--| Tests for `Stream`.

--| The loop a newcomer writes: the first value within `fuel` that satisfies
--| `p`, reading `s.head` and recursing on `s.tail`.
def Stream.Tests.firstWhere (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := match fuel with
  | Zero => None
  | Succ k => if p s.head then Some s.head else Stream.Tests.firstWhere s.tail p k

--| The sum of the first `count` values, by `head` and `tail`.
def Stream.Tests.sumFirst (s: Stream Nat) (count acc: Nat): Nat := match count with
  | Zero => acc
  | Succ k => Stream.Tests.sumFirst s.tail k (acc + s.head)

--| The Fibonacci numbers, by `unfold`.
def Stream.Tests.fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)

test "Stream.take, at" := (Stream.iterate (* 2) 1).take 5 == [1, 2, 4, 8, 16] ∧ (Stream.iterate (* 2) 1).at 10 == 1024

test "Stream.head, tail" :=
  (Stream.iterate (* 2) 1).tail.tail.take 3 == [4, 8, 16] ∧ (Stream.iterate (* 2) 1).tail.tail.tail.tail.tail.head == 32

test "Stream.cons" :=
  (Stream.cons 0 (Stream.iterate (+ 1) 5)).take 3 == [0, 5, 6] ∧ (Stream.cons 0 (Stream.iterate (+ 1) 5)).tail.head == 5

test "Stream.unfold" :=
  Stream.Tests.fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13] ∧ Stream.Tests.fibs.tail.tail.tail.head == 2

test "Stream.map" := ((Stream.iterate (+ 1) 0).map (* 3)).tail.take 3 == [3, 6, 9]

test "Stream of streams" := (Stream.iterate (s => s.map (+ 1)) (Stream.iterate (* 2) 1)).tail.tail.head.tail.head == 4

test "Stream head and tail loop: firstWhere" :=
  Stream.Tests.firstWhere (Stream.iterate (+ 1) 0) (n => n * n > 50) 1000 == Some 8
    ∧ Stream.Tests.firstWhere (Stream.iterate (+ 1) 0) (n => n > 50) 10 == None

-- 20,000 tails: quadratic, this would take minutes; linear, well under a second.
test "Stream head and tail loop: sum" := Stream.Tests.sumFirst (Stream.iterate (+ 1) 0) 20000 0 == 199990000

test "Stream.zipWith" :=
  (Stream.iterate (+ 1) 0).zipWith (Stream.iterate (* 2) 1) (+)
    |> (z => z.take 4 == [1, 3, 6, 11] ∧ z.tail.tail.head == 6)

test "Stream.drop" := (Stream.iterate (+ 1) 0).drop 5 |> (d => d.take 3 == [5, 6, 7] ∧ d.head == 5)

test "Stream.interleave" :=
  Stream.interleave (Stream.iterate (+ 2) 0) (Stream.iterate (+ 2) 1)
    |> (i => i.take 6 == [0, 1, 2, 3, 4, 5] ∧ i.at 7 == 7)

test "Stream.repeat, fromFn" :=
  (Stream.repeat 7).take 3 == [7, 7, 7]
    ∧ (Stream.fromFn (n => n * n)).take 4 == [0, 1, 4, 9]
    ∧ (Stream.fromFn (n => n * n)).tail.head == 1

test "Stream.scan" := (Stream.iterate (+ 1) 1).scan 0 (+) |> (s => s.take 5 == [0, 1, 3, 6, 10] ∧ s.tail.tail.head == 3)

test "Stream.find" :=
  (Stream.iterate (+ 1) 0).find 100 (n => n * n > 50) == Some 8 ∧ (Stream.iterate (+ 1) 0).find 5 (n => n > 50) == None

test "Stream.fold" := (Stream.iterate (+ 1) 1).fold 4 0 (+) == 10

-- 20,000 values each: read by walk or front, these take well under a second; read by `at` they would not.
test "Stream.take: 20,000 values" := ((Stream.iterate (+ 1) 0).take 20000).length == 20000

test "Stream.find: 20,000 values" := (Stream.iterate (+ 1) 0).find 20000 (n => n == 19999) == Some 19999

test "Stream.fold: 20,000 values" := (Stream.iterate (+ 1) 0).fold 20000 0 (+) == 199990000

test "Stream.findRepeat" :=
  (Stream.iterate (n => (n * n + 1) % 7) 0).findRepeat 100 == Some (3, 4)
    ∧ (Stream.iterate (+ 1) 0).findRepeat 100 == None
    ∧ (Stream.iterate (n => (n + 1) % 5) 0).findRepeat 5 == None
    ∧ (Stream.iterate (n => (n + 1) % 5) 0).findRepeat 6 == Some (0, 5)

-- A cycle of 20,000 states, found by one walk with a map of what was seen.
test "Stream.findRepeat: a cycle after 20,000 steps" :=
  (Stream.iterate (n => (n + 1) % 20000) 0).findRepeat 40000 == Some (0, 20000)

test "Stream.findIndex" :=
  (Stream.iterate (+ 1) 0).findIndex 100 (n => n * n > 50) == Some 8
    ∧ (Stream.iterate (+ 1) 0).findIndex 5 (n => n > 50) == None
    ∧ (Stream.iterate (+ 3) 0).tail.findIndex 10 (n => n == 9) == Some 2

test "Stream.foldUntil" :=
  (Stream.iterate (+ 1) 1).foldUntil 100 0 (+) (total => total > 20) == (21, 6)
    ∧ (Stream.iterate (+ 1) 1).foldUntil 3 0 (+) (total => total > 20) == (6, 3)

--| A step that is slow: a hundred additions to add one.
def Stream.Tests.slowStep (x: Nat): Nat := Nat.iterate 100 (+ 1) x - 99

-- The same 20,000 values with a slow step: `fold` reads the walk once, a head and tail loop pays the re-walk too.
test "Stream.fold: a slow step, 20,000 values" := (Stream.iterate Stream.Tests.slowStep 0).fold 20000 0 (+) == 199990000

test "Stream head and tail loop: a slow step, 20,000 values" :=
  Stream.Tests.sumFirst (Stream.iterate Stream.Tests.slowStep 0) 20000 0 == 199990000

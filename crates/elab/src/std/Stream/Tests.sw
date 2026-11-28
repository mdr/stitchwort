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

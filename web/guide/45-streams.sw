import Std (Stream)

-- A `Stream a` goes on forever. You never build it by writing it out:
-- `iterate` repeats a step from a first value, and `unfold` runs a step
-- that gives a value and the next state (here, the pair of Fibonacci
-- numbers it has got to). `take n` shows the first `n` values.
def powers: Stream Nat := Stream.iterate (* 2) 1

def fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)

test "the first values" := powers.take 5 == [1, 2, 4, 8, 16] ∧ fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13]

-- Reading a stream is recursion on its head and tail, as over a list. A
-- stream has no end, so a number that counts down is what shrinks: the loop
-- gives up when it reaches zero.
def firstWhere (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := match fuel with
  | Zero => None
  | Succ k => if p s.head then Some s.head else firstWhere s.tail p k

test "the first power of two above 100" := firstWhere powers (n => n > 100) 20 == Some 128

-- Two streams with the same value at every position are equal, which is how
-- laws are proved. Mapping twice is mapping once with both steps, and
-- comparing position by position computes.
theorem mapMap ∀ (s: Stream a) (f: a → b) (g: b → c): (s.map f).map g = s.map (x => g (f x)) :=
  Stream.ext ((s.map f).map g) (s.map (x => g (f x))) (n => byComputing)

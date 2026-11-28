-- Chapter 7: infinite streams.
import Std (Eq, List, Nat, Option, Stream)

-- begin build
def powers: Stream Nat := Stream.iterate (* 2) 1

def fibs: Stream Nat := Stream.unfold (p => (p.fst, (p.snd, p.fst + p.snd))) (0, 1)

def sevens: Stream Nat := Stream.repeat 7

test "building streams" :=
  powers.take 5 == [1, 2, 4, 8, 16] ∧ fibs.take 8 == [0, 1, 1, 2, 3, 5, 8, 13] ∧ sevens.take 3 == [7, 7, 7]
-- end build

-- begin head-tail
def firstWhere (s: Stream a) (p: a → Bool) (fuel: Nat): Option a := match fuel with
  | Zero => None
  | Succ k => if p s.head then Some s.head else firstWhere s.tail p k

def sumFirst (s: Stream Nat) (count total: Nat): Nat := match count with
  | Zero => total
  | Succ k => sumFirst s.tail k (total + s.head)

test "head and tail" :=
  firstWhere powers (n => n > 100) 20 == Some 128 ∧ sumFirst (Stream.iterate (+ 1) 0) 20000 0 == 199990000
-- end head-tail

-- begin take-find
test "take and find" :=
  fibs.take 5 == [0, 1, 1, 2, 3]
    ∧ fibs.find 50 (n => n > 1000) == Some 1597
    ∧ fibs.find 5 (n => n > 1000) == None
    ∧ powers.fold 4 0 (+) == 15
-- end take-find

-- begin find-repeat
def squares: Stream Nat := Stream.iterate (n => (n * n + 1) % 7) 0

test "find a repeat" :=
  squares.take 6 == [0, 1, 2, 5, 5, 5]
    ∧ squares.findRepeat 100 == Some (3, 4)
    ∧ (Stream.iterate (+ 1) 0).findRepeat 100 == None
    ∧ (Stream.iterate (+ 1) 1).foldUntil 100 0 (+) (total => total > 20) == (21, 6)
-- end find-repeat

-- begin proof
theorem mapMap ∀ (s: Stream a) (f: a → b) (g: b → c): (s.map f).map g = s.map (x => g (f x)) :=
  Stream.ext ((s.map f).map g) (s.map (x => g (f x))) (n => byComputing)
-- end proof

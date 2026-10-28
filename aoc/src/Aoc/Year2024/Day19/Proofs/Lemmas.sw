-- List facts the proofs use: what `startsWith` says about a list, and
-- counting over `flatMap`.

namespace Aoc.Year2024.Day19.Proofs
import Aoc.Year2024.Day19 (startsWith)
import Std (Bool, DecEq, Eq, List, Nat, Void)

-- Dropping a list's start leaves what was appended to it.
theorem dropAppend: (start: List a) → (rest: List a) → (List.append start rest).drop start.length = rest
  | Nil, rest => rfl
  | Cons first others, rest => dropAppend others rest

-- A list starts with what was appended to.
theorem startsWithAppend [auto decEq: DecEq a]: (start: List a) → (rest: List a) → startsWith (List.append start rest) start = True
  | Nil, rest => rfl
  | Cons first others, rest => rewrite DecEq.refl first, startsWithAppend others rest in rfl

-- A list that starts with `start` is `start`, then the rest of it.
theorem startsWithSplit [auto decEq: DecEq a]: (whole: List a) → (start: List a) → startsWith whole start = True →
    List.append start (whole.drop start.length) = whole
  | whole, Nil, starts => rfl
  | Nil, Cons first others, starts => Void.exfalso (Bool.falseNotTrue starts)
  | Cons wholeFirst wholeRest, Cons first others, starts =>
    rewrite DecEq.sound wholeFirst first (Bool.andLeft _ _ starts), startsWithSplit wholeRest others (Bool.andRight _ _ starts) in rfl

-- A start is no longer than the list.
theorem startsWithLength [auto decEq: DecEq a] (whole: List a) (start: List a) (starts: startsWith whole start = True):
    start.length ≤ whole.length :=
  omega [List.lengthAppend start (whole.drop start.length), Eq.cong List.length (startsWithSplit whole start starts)]

-- Appending to `start` gives `whole` exactly when the appended list is the
-- rest of `whole`, once `whole` starts with `start`.
theorem appendEqDrop [auto decEq: DecEq a] (whole: List a) (start: List a) (starts: startsWith whole start = True) (rest: List a):
    (List.append start rest == whole) = (rest == whole.drop start.length) :=
  match same: rest == whole.drop start.length with
    | True => rewrite DecEq.sound rest (whole.drop start.length) same, startsWithSplit whole start starts in DecEq.refl whole
    | False =>
      match made: List.append start rest == whole with
        | True =>
          let dropped := Eq.trans (Eq.sym (dropAppend start rest)) (Eq.cong (list => list.drop start.length) (DecEq.sound _ _ made))
          Void.exfalso (DecEq.soundFalse rest (whole.drop start.length) same dropped)
        | False => rfl

-- Nothing appended to `start` gives a list that doesn't start with it.
theorem appendNotEq [auto decEq: DecEq a] (whole: List a) (start: List a) (starts: startsWith whole start = False) (rest: List a):
    (List.append start rest == whole) = False :=
  match made: List.append start rest == whole with
    | True =>
      let startsAfter: startsWith whole start = True := rewrite <- DecEq.sound _ _ made in startsWithAppend start rest
      Void.exfalso (Bool.falseNotTrue (Eq.trans (Eq.sym starts) startsAfter))
    | False => rfl

-- Counting over a `flatMap` adds up the counts over each part.
theorem countFlatMap (f: a → List b) (passes: b → Bool): (xs: List a) →
    (xs.flatMap f).count passes = xs.sumBy (x => (f x).count passes)
  | Nil => rfl
  | Cons x rest =>
    rewrite List.countAppend (f x) (rest.flatMap f) passes, List.sumByCons rest x (x => (f x).count passes), countFlatMap f passes rest in rfl

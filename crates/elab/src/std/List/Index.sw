-- Lists by index: `List.getOr` (the element at an index, with a default) and
-- its lemmas for append, take, a block written n times, and equality by
-- index. A file of its own, so that programs using only the toolkit don't
-- check these.

-- The element at index i, or `d` past the end.
def List.getOr (d: a): Nat -> List a -> a
  | i,      Nil       => d
  | Zero,   Cons x xs => x
  | Succ i, Cons x xs => List.getOr d i xs

theorem List.getOrExample: List.getOr 0 1 [7, 8] = 8 := rfl

theorem List.getOrAppendLeft (d: a): (i: Nat) -> (xs: List a) -> (ys: List a) -> i < List.length xs ->
    List.getOr d i (List.append xs ys) = List.getOr d i xs
  | i,      Nil,       ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Zero,   Cons x xs, ys, h => rfl
  | Succ i, Cons x xs, ys, h => List.getOrAppendLeft d i xs ys h

theorem List.getOrAppendRight (d: a): (i: Nat) -> (xs: List a) -> (ys: List a) -> List.length xs <= i ->
    List.getOr d i (List.append xs ys) = List.getOr d (i - List.length xs) ys
  | i,      Nil,       ys, h => rfl
  | Zero,   Cons x xs, ys, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ i, Cons x xs, ys, h => List.getOrAppendRight d i xs ys h

theorem List.getOrTake (d: a): (k: Nat) -> (i: Nat) -> (xs: List a) -> i < k -> List.getOr d i (List.take k xs) = List.getOr d i xs
  | Zero,   i,      xs,        h => Void.exfalso (Bool.falseNotTrue h)
  | Succ k, i,      Nil,       h => rfl
  | Succ k, Zero,   Cons x xs, h => rfl
  | Succ k, Succ i, Cons x xs, h => List.getOrTake d k i xs h

-- Lists of the same length that agree at every index are equal.
theorem List.extGetOr (d: a): (xs: List a) -> (ys: List a) -> List.length xs = List.length ys ->
    ((i: Nat) -> i < List.length xs -> List.getOr d i xs = List.getOr d i ys) -> xs = ys
  | Nil,       Nil,       e, h => rfl
  | Nil,       Cons y ys, e, h => Void.exfalso (Nat.zeroNotSucc (List.length ys) e)
  | Cons x xs, Nil,       e, h => Void.exfalso (Nat.succNotZero (List.length xs) e)
  | Cons x xs, Cons y ys, e, h =>
    Eq.trans (Eq.cong (z => Cons z xs) (h 0 rfl))
      (Eq.cong (Cons y) (List.extGetOr d xs ys (Nat.succInjective (List.length xs) (List.length ys) e) (i hi => h (Succ i) hi)))

-- Index i of a block of k elements written n times is index `i % k` of the block.
theorem List.getOrConcatReplicate (d: a) (b: List a) (k: Nat) [auto hk: k != 0] (hb: List.length b = k): (n: Nat) -> (i: Nat) -> i < n * k ->
    List.getOr d i (List.concat (List.replicate n b)) = List.getOr d (i % k) b
  | Zero,   i, h => Void.exfalso (Bool.falseNotTrue h)
  | Succ n, i, h =>
    match t: Nat.leq k i with
      | False =>
        calc List.getOr d i (List.append b (List.concat (List.replicate n b)))
          _ = List.getOr d i b       := List.getOrAppendLeft d i b (List.concat (List.replicate n b)) (Nat.ltCongRight i k (List.length b) (Eq.sym hb) (Nat.leqFalse k i t))
          _ = List.getOr d (i % k) b := Eq.cong (y => List.getOr d y b) (Eq.sym (Nat.modSmall i k (Nat.leqFalse k i t)))
      | True =>
        calc List.getOr d i (List.append b (List.concat (List.replicate n b)))
          _ = List.getOr d (i - List.length b) (List.concat (List.replicate n b))
              := List.getOrAppendRight d i b (List.concat (List.replicate n b)) (Nat.leCongLeft k (List.length b) i (Eq.sym hb) t)
          _ = List.getOr d (i - k) (List.concat (List.replicate n b)) := Eq.cong (y => List.getOr d (i - y) (List.concat (List.replicate n b))) hb
          _ = List.getOr d ((i - k) % k) b
              := List.getOrConcatReplicate d b k hb n (i - k) (Nat.subLtAdd i k (n * k) t (Nat.ltCongRight i (k + n * k) (n * k + k) (Nat.addComm k (n * k)) h))
          _ = List.getOr d (i % k) b
              := Eq.cong (y => List.getOr d y b) (Eq.trans (Eq.sym (Nat.addModSelf k (i - k))) (Eq.cong (y => y % k) (Nat.addSubCancel k i t)))


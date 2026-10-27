-- `Map.byPosition xs` looks up like `List.getOr` on `xs`
-- (`Map.getOrByPosition`). Kept out of Map.sw because the proof needs
-- `omega`.

-- No position below `s` is numbered from `s`.
theorem Map.lookupLastBelow (k: Nat): (s: Nat) → (xs: List a) → k < s → Map.lookupLast k (List.withIndexFrom s xs) = None
  | s, Nil, h => rfl
  | s, Cons x xs, h =>
    rewrite Map.lookupLastBelow k (Succ s) xs (omega) in
      match c: Nat.compare k s with
        | Equal => omega [Nat.compareEqual k s c]
        | Less => rfl
        | Greater => rfl

-- Position s + i of the elements numbered from s is element i.
theorem Map.lookupLastWithIndex (d: a): (s: Nat) → (i: Nat) → (xs: List a) →
    Option.getOrElse (Map.lookupLast (s + i) (List.withIndexFrom s xs)) d = List.getOr xs i d
  | s, i, Nil => rfl
  | s, Zero, Cons x xs =>
    rewrite Nat.addZero s, Map.lookupLastBelow s (Succ s) xs (Nat.leRefl (Succ s)), Nat.compareSelf s in rfl
  | s, Succ i, Cons x xs =>
    let ih: Option.getOrElse (Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs)) d = List.getOr xs i d :=
      Map.lookupLastWithIndex d (Succ s) i xs
    rewrite Nat.addSucc s i in
      match r: Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs) with
        | Some v => ih
        | None =>
          match c: Nat.compare (Succ (s + i)) s with
            | Equal => omega [Nat.compareEqual (Succ (s + i)) s c]
            | Less => ih
            | Greater => ih

-- Looking up a position in `Map.byPosition xs` is `List.getOr` on `xs`,
-- inside the list and past its end.
theorem Map.getOrByPosition (xs: List a) (i: Nat) (d: a): Map.getOr (Map.byPosition xs) i d = List.getOr xs i d :=
  rewrite Map.getFromList i (List.withIndex xs) in Map.lookupLastWithIndex d 0 i xs

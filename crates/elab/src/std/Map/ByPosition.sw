--| `Map.byPosition xs` looks up like `List.get` or `List.getOr` on `xs`
--| ([`Map.getByPosition`], [`Map.getOrByPosition`]).
-- Kept out of Map.sw because the proof needs `arithmetic`.

--| No position below `s` is numbered from `s`.
theorem Map.lookupLastBelow ∀ (k s: Nat) (xs: List a) (h: k < s): Map.lookupLast k (List.withIndexFrom s xs) = None :=
  match xs with
    | [] => byComputing
    | [x, ..xs] =>
      rewrite Map.lookupLastBelow k (Succ s) xs (arithmetic) then
        match c: Nat.compare k s with
          | Equal => arithmetic [Nat.compareEqual k s c]
          | Less => byComputing
          | Greater => byComputing

--| Position s + i of the elements numbered from s is element i.
theorem Map.lookupLastWithIndex ∀ (d: a) (s i: Nat) (xs: List a):
    Option.getOrElse (Map.lookupLast (s + i) (List.withIndexFrom s xs)) d = List.getOr xs i d :=
  match i, xs with
    | i, [] => byComputing
    | Zero, [x, ..xs] =>
      rewrite Nat.addZero s, Map.lookupLastBelow s (Succ s) xs (Nat.leRefl (Succ s)), Nat.compareSelf s then byComputing
    | Succ i, [x, ..xs] =>
      let ih: Option.getOrElse (Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs)) d = List.getOr xs i d :=
        Map.lookupLastWithIndex d (Succ s) i xs
      rewrite Nat.addSucc s i then
        match r: Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs) with
          | Some v => ih
          | None =>
            match c: Nat.compare (Succ (s + i)) s with
              | Equal => arithmetic [Nat.compareEqual (Succ (s + i)) s c]
              | Less => ih
              | Greater => ih

--| Looking up a position in `Map.byPosition xs` is `List.getOr` on `xs`,
--| inside the list and past its end.
theorem Map.getOrByPosition ∀ (xs: List a) (i: Nat) (d: a): Map.getOr (Map.byPosition xs) i d = List.getOr xs i d :=
  rewrite Map.getFromList i (List.withIndex xs) then Map.lookupLastWithIndex d 0 i xs

--| Position s + i of the elements numbered from s is element i, if there is
--| one; past the end both are `None`.
theorem Map.lookupLastWithIndexGet ∀ (s i: Nat) (xs: List a):
    Map.lookupLast (s + i) (List.withIndexFrom s xs) = List.get xs i :=
  match i, xs with
    | i, [] => byComputing
    | Zero, [x, ..xs] =>
      rewrite Nat.addZero s, Map.lookupLastBelow s (Succ s) xs (Nat.leRefl (Succ s)), Nat.compareSelf s then byComputing
    | Succ i, [x, ..xs] =>
      rewrite Nat.addSucc s i then
        match r: Map.lookupLast (Succ (s + i)) (List.withIndexFrom (Succ s) xs) with
          | Some v => rewrite <- r then Map.lookupLastWithIndexGet (Succ s) i xs
          | None =>
            match c: Nat.compare (Succ (s + i)) s with
              | Equal => arithmetic [Nat.compareEqual (Succ (s + i)) s c]
              | Less => rewrite <- r then Map.lookupLastWithIndexGet (Succ s) i xs
              | Greater => rewrite <- r then Map.lookupLastWithIndexGet (Succ s) i xs

--| Looking up a position in `Map.byPosition xs` is `List.get` on `xs`, inside
--| the list and past its end. The `getOr` version is [`Map.getOrByPosition`].
theorem Map.getByPosition ∀ (xs: List a) (i: Nat): Map.get (Map.byPosition xs) i = List.get xs i :=
  rewrite Map.getFromList i (List.withIndex xs) then Map.lookupLastWithIndexGet 0 i xs

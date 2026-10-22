-- core/CompareData.sw. The same laws for `List` (lexicographic), `Pair`,
-- `Option`, `Char` and `Text`. Loaded with the core: `List.instOrd`,
-- `Pair.instOrd`, `Option.instOrd`, `Char.instOrd` and `Text.instOrd` need
-- them (docs/proposals/prelude-slim.md §2.1).

-- Lexicographic comparison of lists, by a comparison of their elements:
-- the first difference decides, and a list comes before its extensions.
def List.compareLex (cmp: a -> a -> Ordering): List a -> List a -> Ordering
  | Nil,       Nil       => Equal
  | Nil,       Cons y ys => Less
  | Cons x xs, Nil       => Greater
  | Cons x xs, Cons y ys => Ordering.andThen (cmp x y) (List.compareLex cmp xs ys)

theorem List.compareLexEqual (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y):
    (xs: List a) -> (ys: List a) -> List.compareLex cmp xs ys = Equal -> xs = ys
  | Nil,       Nil,       h => rfl
  | Nil,       Cons y ys, h => Void.exfalso (Ordering.lessNotEqual h)
  | Cons x xs, Nil,       h => Void.exfalso (Ordering.greaterNotEqual h)
  | Cons x xs, Cons y ys, h =>
    Eq.trans (Eq.cong (t => Cons t xs) (equal x y (And.left (Ordering.andThenEqual (cmp x y) (List.compareLex cmp xs ys) h))))
      (Eq.cong (Cons y) (List.compareLexEqual cmp equal xs ys (And.right (Ordering.andThenEqual (cmp x y) (List.compareLex cmp xs ys) h))))

theorem List.compareLexFlip (cmp: a -> a -> Ordering) (flip: (x: a) -> (y: a) -> cmp y x = Ordering.flip (cmp x y)):
    (xs: List a) -> (ys: List a) -> List.compareLex cmp ys xs = Ordering.flip (List.compareLex cmp xs ys)
  | Nil,       Nil       => rfl
  | Nil,       Cons y ys => rfl
  | Cons x xs, Nil       => rfl
  | Cons x xs, Cons y ys =>
    rewrite flip x y, List.compareLexFlip cmp flip xs ys in
      Eq.sym (Ordering.flipAndThen (cmp x y) (List.compareLex cmp xs ys))

theorem List.compareLexTrans (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y)
    (trans: (x: a) -> (y: a) -> (z: a) -> cmp x y = Less -> cmp y z = Less -> cmp x z = Less):
    (xs: List a) -> (ys: List a) -> (zs: List a) ->
    List.compareLex cmp xs ys = Less -> List.compareLex cmp ys zs = Less -> List.compareLex cmp xs zs = Less
  | Nil,       Nil,       zs,        h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | Nil,       Cons y ys, Nil,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Nil,       Cons y ys, Cons z zs, h1, h2 => rfl
  | Cons x xs, Nil,       zs,        h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Cons x xs, Cons y ys, Nil,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Cons x xs, Cons y ys, Cons z zs, h1, h2 =>
    Ordering.andThenTrans (cmp x y) (cmp y z) (cmp x z)
      (List.compareLex cmp xs ys) (List.compareLex cmp ys zs) (List.compareLex cmp xs zs)
      (trans x y z)
      (e => Eq.cong (t => cmp t z) (equal x y e))
      (e => Eq.sym (Eq.cong (t => cmp x t) (equal y z e)))
      (p q => List.compareLexTrans cmp equal trans xs ys zs p q) h1 h2

-- Pairs, by their first parts, then their second.
def Pair.compareWith (ca: a -> a -> Ordering) (cb: b -> b -> Ordering): Pair a b -> Pair a b -> Ordering
  | MkPair x1 y1, MkPair x2 y2 => Ordering.andThen (ca x1 x2) (cb y1 y2)

theorem Pair.compareWithEqual (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (ea: (x: a) -> (y: a) -> ca x y = Equal -> x = y) (eb: (x: b) -> (y: b) -> cb x y = Equal -> x = y):
    (p: Pair a b) -> (q: Pair a b) -> Pair.compareWith ca cb p q = Equal -> p = q
  | MkPair x1 y1, MkPair x2 y2, h =>
    Eq.trans (Eq.cong (t => MkPair t y1) (ea x1 x2 (And.left (Ordering.andThenEqual (ca x1 x2) (cb y1 y2) h))))
      (Eq.cong (MkPair x2) (eb y1 y2 (And.right (Ordering.andThenEqual (ca x1 x2) (cb y1 y2) h))))

theorem Pair.compareWithFlip (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (fa: (x: a) -> (y: a) -> ca y x = Ordering.flip (ca x y)) (fb: (x: b) -> (y: b) -> cb y x = Ordering.flip (cb x y)):
    (p: Pair a b) -> (q: Pair a b) -> Pair.compareWith ca cb q p = Ordering.flip (Pair.compareWith ca cb p q)
  | MkPair x1 y1, MkPair x2 y2 =>
    rewrite fa x1 x2, fb y1 y2 in Eq.sym (Ordering.flipAndThen (ca x1 x2) (cb y1 y2))

theorem Pair.compareWithTrans (ca: a -> a -> Ordering) (cb: b -> b -> Ordering)
    (ea: (x: a) -> (y: a) -> ca x y = Equal -> x = y)
    (ta: (x: a) -> (y: a) -> (z: a) -> ca x y = Less -> ca y z = Less -> ca x z = Less)
    (tb: (x: b) -> (y: b) -> (z: b) -> cb x y = Less -> cb y z = Less -> cb x z = Less):
    (p: Pair a b) -> (q: Pair a b) -> (r: Pair a b) ->
    Pair.compareWith ca cb p q = Less -> Pair.compareWith ca cb q r = Less -> Pair.compareWith ca cb p r = Less
  | MkPair x1 y1, MkPair x2 y2, MkPair x3 y3, h1, h2 =>
    Ordering.andThenTrans (ca x1 x2) (ca x2 x3) (ca x1 x3) (cb y1 y2) (cb y2 y3) (cb y1 y3)
      (ta x1 x2 x3)
      (e => Eq.cong (t => ca t x3) (ea x1 x2 e))
      (e => Eq.sym (Eq.cong (t => ca x1 t) (ea x2 x3 e)))
      (tb y1 y2 y3) h1 h2

-- Optional values: `None` first.
def Option.compareWith (cmp: a -> a -> Ordering): Option a -> Option a -> Ordering
  | None, None => Equal
  | None, Some y  => Less
  | Some x,  None => Greater
  | Some x,  Some y  => cmp x y

theorem Option.compareWithEqual (cmp: a -> a -> Ordering) (equal: (x: a) -> (y: a) -> cmp x y = Equal -> x = y):
    (m: Option a) -> (n: Option a) -> Option.compareWith cmp m n = Equal -> m = n
  | None, None, h => rfl
  | None, Some y,  h => Void.exfalso (Ordering.lessNotEqual h)
  | Some x,  None, h => Void.exfalso (Ordering.greaterNotEqual h)
  | Some x,  Some y,  h => Eq.cong Some (equal x y h)

theorem Option.compareWithFlip (cmp: a -> a -> Ordering) (flip: (x: a) -> (y: a) -> cmp y x = Ordering.flip (cmp x y)):
    (m: Option a) -> (n: Option a) -> Option.compareWith cmp n m = Ordering.flip (Option.compareWith cmp m n)
  | None, None => rfl
  | None, Some y  => rfl
  | Some x,  None => rfl
  | Some x,  Some y  => flip x y

theorem Option.compareWithTrans (cmp: a -> a -> Ordering)
    (trans: (x: a) -> (y: a) -> (z: a) -> cmp x y = Less -> cmp y z = Less -> cmp x z = Less):
    (m: Option a) -> (n: Option a) -> (o: Option a) ->
    Option.compareWith cmp m n = Less -> Option.compareWith cmp n o = Less -> Option.compareWith cmp m o = Less
  | None, None, o,       h1, h2 => Void.exfalso (Ordering.equalNotLess h1)
  | None, Some y,  None, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | None, Some y,  Some z,  h1, h2 => rfl
  | Some x,  None, o,       h1, h2 => Void.exfalso (Ordering.greaterNotLess h1)
  | Some x,  Some y,  None, h1, h2 => Void.exfalso (Ordering.greaterNotLess h2)
  | Some x,  Some y,  Some z,  h1, h2 => trans x y z h1 h2

-- Characters, by scalar value.
def Char.compare (x: Char) (y: Char): Ordering := Nat.compare (Char.toNat x) (Char.toNat y)

theorem Char.compareEqual (x: Char) (y: Char) (h: Char.compare x y = Equal): x = y :=
  Char.ext x y (Nat.compareEqual (Char.toNat x) (Char.toNat y) h)

theorem Char.compareFlip (x: Char) (y: Char): Char.compare y x = Ordering.flip (Char.compare x y) :=
  Nat.compareFlip (Char.toNat x) (Char.toNat y)

theorem Char.compareTrans (x: Char) (y: Char) (z: Char) (h1: Char.compare x y = Less) (h2: Char.compare y z = Less):
    Char.compare x z = Less :=
  Nat.compareTrans (Char.toNat x) (Char.toNat y) (Char.toNat z) h1 h2

-- `Text.compare` is lexicographic by characters: `List.compareLex` with
-- `Char.compare`, step for step. So its laws are the list's.
theorem Text.compareCharsLex: (xs: List Char) -> (ys: List Char) -> Text.compareChars xs ys = List.compareLex Char.compare xs ys
  | Nil,       Nil       => rfl
  | Nil,       Cons y ys => rfl
  | Cons x xs, Nil       => rfl
  | Cons x xs, Cons y ys => Eq.cong (r => Ordering.andThen (Char.compare x y) r) (Text.compareCharsLex xs ys)

theorem Text.ext: (s: Text) -> (t: Text) -> Text.toList s = Text.toList t -> s = t
  | MkText a, MkText b, h => Eq.cong MkText h

theorem Text.compareEqual (s: Text) (t: Text) (h: Text.compare s t = Equal): s = t :=
  Text.ext s t (List.compareLexEqual Char.compare Char.compareEqual (Text.toList s) (Text.toList t)
    (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t))) h))

theorem Text.compareFlip (s: Text) (t: Text): Text.compare t s = Ordering.flip (Text.compare s t) :=
  Eq.trans (Text.compareCharsLex (Text.toList t) (Text.toList s))
    (Eq.trans (List.compareLexFlip Char.compare Char.compareFlip (Text.toList s) (Text.toList t))
      (Eq.cong Ordering.flip (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t)))))

theorem Text.compareTrans (s: Text) (t: Text) (u: Text) (h1: Text.compare s t = Less) (h2: Text.compare t u = Less):
    Text.compare s u = Less :=
  Eq.trans (Text.compareCharsLex (Text.toList s) (Text.toList u))
    (List.compareLexTrans Char.compare Char.compareEqual Char.compareTrans (Text.toList s) (Text.toList t) (Text.toList u)
      (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList s) (Text.toList t))) h1)
      (Eq.trans (Eq.sym (Text.compareCharsLex (Text.toList t) (Text.toList u))) h2))


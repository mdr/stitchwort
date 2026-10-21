-- `match e: x` on a scrutinee with an `auto` dictionary (SW-188): the
-- scrutinee is found in the goal and in `h` without writing `[ord := ord]`.
-- (The ticket's report doesn't fail on current main, where an application's
-- dictionary is found as soon as its arguments fix the type.)

def pick [auto ord: Ord k] (x: k) (y: k): Nat := match Ord.compare x y with
  | Less => 0
  | _    => 1

theorem pickLess [auto ord: Ord k] (x: k) (y: k) (h: Ord.compare x y = Less): pick x y = 0 :=
  match e: Ord.compare x y with
    | Less    => rfl
    | Equal   => Void.exfalso (Ordering.equalNotLess h)
    | Greater => Void.exfalso (Ordering.greaterNotLess h)

-- `rewrite` with a proof about the same expression has the same need, and
-- already waited for the dictionary.
theorem pickRewrite [auto ord: Ord k] (x: k) (y: k) (h: Ord.compare x y = Less):
    (match Ord.compare x y with | Less => 0 | _ => 1) = 0 := rewrite h in rfl

-- A hole in each branch of a `match`: in each, the matched variable is the
-- branch's constructor, in the goal and in the names' types. A goal is
-- the statement with it put in (`Succ k + 0 = Succ k`), and a second line
-- says what that computes to.
theorem addZero ∀ (n: Nat): n + 0 = n := match n with
  | Zero => ?
  | Succ k => ?

-- A hole in each branch of a `match`: in each, the matched variable is the
-- branch's constructor, in the goal and in the names' types. Goals are
-- shown computed: `Succ k + 0` is shown as `Succ (k + 0)`.
theorem addZero (n: Nat): n + 0 = n :=
  match n with
    | Zero => ?
    | Succ k => ?

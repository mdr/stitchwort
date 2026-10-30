-- `Finite.check`: a statement about every value of a finite type, checked
-- by computing it for each one (docs/proposals/decide.md §6.2). The
-- interface and its instances are in the core (core/Finite.sw), since
-- derived instances need them; this isn't.

-- What `p` says of every value on the list `Finite.all`, it says of every
-- value. `checked` is usually `rfl`: the kernel computes `p` for each value.
-- For a statement over several variables, make them one value: a record or
-- a pair of finite types is finite (`Finite.check (((x, y)) => …) rfl (x, y)`).
-- It is the way past `cases`' budget of 64 cases: 2^16 cases is a list of
-- 65,536 values, checked in seconds, and the proof stays this one term.
theorem Finite.check [auto fin: Finite a] (p: a → Bool) (checked: List.all Finite.all p = True) (x: a): p x = True :=
  List.memOfAll (y => p y = True) Finite.all (List.allToAll p Finite.all checked) x (Finite.complete x)

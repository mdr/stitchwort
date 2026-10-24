-- A hole in the `return` clause of a `match reify`: the goal says what it
-- says in the statement, with the computation that returned `y` in it, not
-- the handlers unfolded. In an operation's clause the goal is short.
import Std (Fail, Result)

theorem toResultThen (t: () -> {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k (t ())) = Result.flatMap (x => Fail.toResult (() => k x)) (Fail.toResult t) :=
  match reify t with
    | return y => ?
    | Fail.stop msg, _ => ?

-- A thunk written in place, in an equation: the goal there is already
-- computed when the split starts (the equation instantiated the statement),
-- so only the computation is replaced by `y`; the handlers stay unfolded.
theorem toResultMap (f: a -> {Fail} b): (xs: List a) ->
    Fail.toResult (() => xs.map f) = Result.traverse (x => Fail.toResult (() => f x)) xs
  | [] => rfl
  | [x, ..xs] =>
    match reify (() => f x) with
      | return y => ?
      | Fail.stop msg, _ => rfl

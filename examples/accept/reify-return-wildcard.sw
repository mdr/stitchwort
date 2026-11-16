-- `match reify`'s `return` clause may write `_` for the result when the
-- clause doesn't use it, as a handler's `return` clause may.

import Std (Fail, Option, Result)

theorem toOptionToResult ∀ (t: () → {Fail} a): Fail.toOption t = Result.toOption (Fail.toResult t) := match reify t with
  | return _ => byComputing
  | Fail.stop msg, _ => byComputing

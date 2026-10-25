-- A computation can do different things, so a fact about any computation
-- splits on what it does first. `match reify` does that, and is only for
-- proofs. Here `t` is any thunk that may fail; `Fail.toOption` handles it.
import Std (Fail, Option)
import Std.Fail (toOption)

-- Whatever `t` does, handling it and then adding 1 to the result is the
-- same as handling `t` and adding 1 to what it gave.
theorem toOptionPlusOne (t: () -> {Fail} Nat):
    toOption (() => t () + 1) = Option.map (toOption t) (n => n + 1) :=
  match reify t with
    | return n => rfl -- `t` finished with `n`
    | Fail.stop message, _ => rfl -- `t` failed with `message`

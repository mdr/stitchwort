-- expect-error: E-TYPE-MISMATCH
-- An arm is checked even where its constructor can't be: `FSucc j` is
-- impossible in a `Fin 1`, but its right side still has to be a `Nat`.
import Std (Fin)

def bad: Fin 1 → Nat
  | FZero => 4
  | FSucc j if True => "bad"

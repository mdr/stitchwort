-- expect-error: E-REWRITE-NOTHING
-- `Nat.mulOne n` is `n * 1 = n`: written the other way round it looks for the
-- bare variable `n`, which occurs in the goal. A bare variable has no outer
-- function to search for, so that occurrence isn't evidence the direction is
-- wrong: the note about `<-` stays last, after the goal and search notes.
import Std (Nat)

theorem twice (n: Nat): 2 * n = n :=
  rewrite Nat.mulOne n in rfl

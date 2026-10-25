-- expect-error: E-PROOF-ONLY
-- `reify` only in a proof (D1147): `finished` computes a `Bool`, so it would
-- run, and its answer would depend on how the computation is represented.
import Std (Fail)

def finished (t: () → {Fail} a): Bool :=
  match reify t with
    | return x => True
    | Fail.stop msg, _ => False

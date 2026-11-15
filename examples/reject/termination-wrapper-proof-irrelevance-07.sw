-- expect-error: E-TERMINATION
-- The soundness corpus's proof-irrelevance-07, kept beside the wrapper
-- rule's other tests: `MkBox`'s one field is a proof, so it isn't a
-- wrapper. Comparison skips proofs, so every `Box Loop` is the same value
-- to the kernel, and `MkBox n` with `n` a part of the proof `l` isn't
-- smaller than `b` (Agda #8699's trap). Partner: `Loop.empty` in
-- accept/self-referential-prop.sw, which recurses on the proof itself.
import Std (Void)

type Box (a: Prop): Type = | MkBox (h: a)

type Loop: Prop = | MkLoop (next: Loop)

def f (b: Box Loop): Void := match b with
  | MkBox l =>
    match l with
      | MkLoop n => f (MkBox n)

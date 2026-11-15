-- expect-error: E-UNIVERSE
-- A wrapper over a parameter in `Type` can't be given a proposition:
-- universes are exact, so its field, declared in `Type`, never holds a
-- proof, and the wrapper rule can read the field's sort from the
-- declaration.
import Std (Void)

type W (a: Type): Type = | MkW (x: a)

type Loop: Prop = | MkLoop (next: Loop)

def f (b: W Loop): Void := match b with
  | MkW l =>
    match l with
      | MkLoop n => f (MkW n)

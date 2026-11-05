-- expect-error: E-TERMINATION
-- Descent is read from real matches, never from a proof field that
-- comparison skips (Agda #8699's lesson): `MkBox n` isn't smaller than `b`.
-- Partner: `Loop.empty` in accept/self-referential-prop.sw.
import Std (Void)

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

type Loop: Prop =
  | MkLoop (next: Loop)

def f (b: Box Loop): Void :=
  match b with
    | MkBox l => match l with
      | MkLoop n => f (MkBox n)

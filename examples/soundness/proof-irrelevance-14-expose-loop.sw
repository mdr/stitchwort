-- expect-error: E-TERMINATION
-- A computing `Prop.irrel` manufactures a constructor from a stuck proof,
-- and that never counts as descent: `n` is part of `Loop.expose l`, not of
-- `l`. Partner: `Loop.expose` and `exposeComputes` in
-- accept/proof-irrelevance.sw. `boxEq` and `Prop.irrel` are `def`s so that
-- they compute: a theorem is sealed (D3722).
import Std (Void)

type Box (a: Prop): Type =
  | MkBox (h: a)

def Box.unbox [a: Prop]: Box a → a
  | MkBox h => h

type Loop: Prop =
  | MkLoop (next: Loop)

def Loop.inv: Loop → Loop
  | MkLoop n => n

def boxEq (a: Prop) (p: a) (q: a): MkBox p = MkBox q := byComputing

def Prop.irrel (a: Prop) (p: a) (q: a): p = q :=
  J (y e2 => p = Box.unbox y) byComputing (boxEq a p q)

def Loop.expose (l: Loop): Loop :=
  J (y e => Loop) (MkLoop (Loop.inv l)) (Prop.irrel Loop (MkLoop (Loop.inv l)) l)

def bad (l: Loop): Void :=
  match Loop.expose l with
    | MkLoop n => bad n

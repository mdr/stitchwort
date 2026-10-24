-- Laws of computations whose proofs need function extensionality: the rest of
-- a `Call` is a function, and two of them are equal when they agree at every
-- result (`Quot.funext`, so `Quot.sound` is the one axiom these use). The laws
-- that don't need it, `Effect.foldCompDone` and `Effect.runPureBind`, are in
-- core/Effect.sw (docs/proposals/effect-polymorphism.md, "Proof tooling").

import Effect (Comp, foldComp, bind)
import Effect.Comp (Done, Call)

-- Sequencing with `Done` changes nothing. (`bind (Done x) next = next x` holds
-- by definition.)
theorem Effect.bindDone [op: Type] [res: op -> Type] [a: Type]:
    (computation: Comp op res a) -> bind computation Done = computation
  | Done x => rfl
  | Call o rest =>
    let pointwise: (y: res o) -> bind (rest y) Done = rest y := y => Effect.bindDone (rest y)
    let same := Quot.funext (res o) (y => Comp op res a) (y => bind (rest y) Done) rest pointwise
    Eq.cong (Call o) same

-- Sequencing is associative.
theorem Effect.bindAssoc [op: Type] [res: op -> Type] [a b r: Type]
    (first: a -> Comp op res b) (second: b -> Comp op res r):
    (computation: Comp op res a) ->
    bind (bind computation first) second = bind computation (x => bind (first x) second)
  | Done x => rfl
  | Call o rest =>
    let pointwise: (y: res o) -> bind (bind (rest y) first) second = bind (rest y) (x => bind (first x) second) :=
      y => Effect.bindAssoc first second (rest y)
    let same :=
      Quot.funext
        (res o)
        (y => Comp op res r)
        (y => bind (bind (rest y) first) second)
        (y => bind (rest y) (x => bind (first x) second))
        pointwise
    Eq.cong (Call o) same

-- Handler fusion: folding a sequence folds its first part, with folding the
-- rest as what to do with each result.
theorem Effect.foldCompBind [op: Type] [res: op -> Type] [a b r: Type]
    (done: b -> r) (call: (o: op) -> (res o -> r) -> r) (next: a -> Comp op res b):
    (computation: Comp op res a) ->
    foldComp done call (bind computation next) = foldComp (x => foldComp done call (next x)) call computation
  | Done x => rfl
  | Call o rest =>
    let pointwise: (y: res o) -> foldComp done call (bind (rest y) next) = foldComp (x => foldComp done call (next x)) call (rest y) :=
      y => Effect.foldCompBind done call next (rest y)
    let same :=
      Quot.funext
        (res o)
        (y => r)
        (y => foldComp done call (bind (rest y) next))
        (y => foldComp (x => foldComp done call (next x)) call (rest y))
        pointwise
    Eq.cong (call o) same

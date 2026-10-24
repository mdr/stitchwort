-- A computation passed where a computation is expected is passed as it is,
-- not run in place and re-wrapped as `Done (runPure c)` (stage 0 of
-- docs/proposals/effect-polymorphism.md). `isDone` sees exactly what it's
-- given: a written `Done` is `Done`, and a computation that is `Done` only
-- once it computes is `Done` once it computes. The matching
-- `reject/effect-pass-*.sw` files check that an arbitrary computation is not
-- known to be `Done`, on each path that once ran it in place.
import Std (Effect, List, Eq)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

def stuckComp: List Nat -> Effect.Comp Effect.NoOp Effect.NoRes Nat
  | Nil => 0
  | Cons x xs => 1

def identityComp (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := computation

-- A name for the type, so dot notation finds `Thunk.finished`.
def Thunk: Type := Effect.Comp Effect.NoOp Effect.NoRes Nat

def Thunk.finished (computation: Thunk): Bool := isDone computation

-- Dot notation on a variable of that type.
def finishedOf (thunk: Thunk): Bool := thunk.finished

type Box =
  | MkBox (content: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def boxDone: Box -> Bool
  | MkBox content => isDone content

type Labelled =
  | MkLabelled (label: Nat) (inner: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def labelledDone: Labelled -> Bool
  | MkLabelled label inner => isDone inner

def allDone: List (Effect.Comp Effect.NoOp Effect.NoRes Nat) -> Bool
  | Nil => True
  | Cons first rest => isDone first && allDone rest

def pairDone: (Nat, Effect.Comp Effect.NoOp Effect.NoRes Nat) -> Bool
  | (label, inner) => isDone inner

def passOn (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := computation

-- A direct argument.
theorem directDone: isDone (Done 3) = True := rfl
theorem directComputes: isDone (stuckComp Nil) = True := rfl

-- A piped argument.
theorem pipedDone: (Done 3 |> isDone) = True := rfl
theorem pipedComputes: (stuckComp Nil |> isDone) = True := rfl

-- A dot call's receiver.
theorem dotDone: (Done 3: Thunk).finished = True := rfl
theorem dotComputes: finishedOf (stuckComp Nil) = True := rfl

-- A constructor's field, by position and by name.
theorem fieldDone: boxDone (MkBox (Done 3)) = True := rfl
theorem fieldComputes: boxDone (MkBox (stuckComp Nil)) = True := rfl
theorem namedFieldDone: labelledDone (MkLabelled { label = 1, inner = Done 3 }) = True := rfl
theorem namedFieldComputes: labelledDone (MkLabelled { label = 1, inner = stuckComp Nil }) = True := rfl

-- A field of a record literal.
type Holder = { inner: Effect.Comp Effect.NoOp Effect.NoRes Nat }

def holderDone (holder: Holder): Bool := isDone holder.inner

theorem recordDone: holderDone { inner = Done 3 } = True := rfl
theorem recordComputes: holderDone { inner = stuckComp Nil } = True := rfl

-- An argument given by name.
def takes (count: Nat) (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Bool := isDone computation

theorem namedArgumentDone: takes (computation := Done 3) (count := 1) = True := rfl
theorem namedArgumentComputes: takes (computation := stuckComp Nil) (count := 1) = True := rfl

-- Items of a list and parts of a tuple.
theorem listDone: allDone [Done 3, Done 4] = True := rfl
theorem listComputes: allDone [stuckComp Nil] = True := rfl
theorem tupleDone: pairDone (1, Done 3) = True := rfl
theorem tupleComputes: pairDone (1, stuckComp Nil) = True := rfl

-- Through a function that takes and returns a computation.
theorem identityDone: isDone (identityComp (Done 3)) = True := rfl
theorem identityComputes: isDone (identityComp (stuckComp Nil)) = True := rfl
theorem bodyDone: isDone (passOn (Done 3)) = True := rfl

-- A written `Done` is a computation where one is expected, so `runPure` takes
-- it (it was refused while the argument was run in place).
export def runIdentity (n: Nat): Nat := Effect.runPure (identityComp (Done n))

test "runPure of a passed computation" := runIdentity 4 == 4

-- `bind` at the empty row, with its arguments passed: the law is stated and
-- proved by cases on the computation.
theorem runPureBindHere [a b: Type]:
    (computation: Effect.Comp Effect.NoOp Effect.NoRes a) -> (next: a -> Effect.Comp Effect.NoOp Effect.NoRes b) ->
    Effect.runPure (Effect.bind computation next) = Effect.runPure (next (Effect.runPure computation))
  | Done x, next => rfl
  | Call () rest, next

-- `mapIn` with a pure function, run, is `map`: the proof uses the library's
-- `runPureBind` on the stuck `mapIn f xs` (probe 3 of the note).
theorem mapInIsMap (f: Nat -> Nat): (xs: List Nat) -> Effect.runPure (List.mapIn f xs) = List.map f xs
  | Nil => rfl
  | Cons x xs =>
    Eq.trans
      (Effect.runPureBind (List.mapIn f xs) (rest => Done (Cons (f x) rest)))
      (Eq.cong (Cons (f x)) (mapInIsMap f xs))

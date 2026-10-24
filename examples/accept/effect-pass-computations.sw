-- A computation passed where a computation is expected is passed as it is,
-- not run in place and re-wrapped as `Done (runPure c)` (stage 0 of
-- docs/proposals/effect-polymorphism.md). `IsDone` sees exactly what it's
-- given: a written `Done` is `Done`, and a computation that is `Done` only
-- once it computes is `Done` once it computes. The matching
-- `reject/effect-pass-*.sw` files check that an arbitrary computation is not
-- known to be `Done`, on each path that once ran it in place.
-- A program can't take a computation apart (docs/proposals/proof-reification.md,
-- stage R2), so the predicate `IsDone` is a `Prop` and the checks are theorems.
import Std (Effect, List, Eq)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
  | Done value => Unit
  | Call () rest

def stuckComp: List Nat -> Effect.Comp Effect.NoOp Effect.NoRes Nat
  | Nil => 0
  | Cons x xs => 1

def identityComp (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := computation

-- A name for the type, so dot notation finds `Thunk.finished`.
def Thunk: Type := Effect.Comp Effect.NoOp Effect.NoRes Nat

def Thunk.finished (computation: Thunk): Prop := IsDone computation

-- Dot notation on a variable of that type.
def finishedOf (thunk: Thunk): Prop := thunk.finished

type Box =
  | MkBox (content: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def boxDone: Box -> Prop
  | MkBox content => IsDone content

type Labelled =
  | MkLabelled (label: Nat) (inner: Effect.Comp Effect.NoOp Effect.NoRes Nat)

def labelledDone: Labelled -> Prop
  | MkLabelled label inner => IsDone inner

def allDone: List (Effect.Comp Effect.NoOp Effect.NoRes Nat) -> Prop
  | Nil => Unit
  | Cons first rest => And (IsDone first) (allDone rest)

def pairDone: (Nat, Effect.Comp Effect.NoOp Effect.NoRes Nat) -> Prop
  | (label, inner) => IsDone inner

def passOn (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := computation

-- A direct argument.
theorem directDone: IsDone (Done 3) := Trivial
theorem directComputes: IsDone (stuckComp Nil) := Trivial

-- A piped argument.
theorem pipedDone: (Done 3 |> IsDone) := Trivial
theorem pipedComputes: (stuckComp Nil |> IsDone) := Trivial

-- A dot call's receiver.
theorem dotDone: (Done 3: Thunk).finished := Trivial
theorem dotComputes: finishedOf (stuckComp Nil) := Trivial

-- A constructor's field, by position and by name.
theorem fieldDone: boxDone (MkBox (Done 3)) := Trivial
theorem fieldComputes: boxDone (MkBox (stuckComp Nil)) := Trivial
theorem namedFieldDone: labelledDone (MkLabelled { label = 1, inner = Done 3 }) := Trivial
theorem namedFieldComputes: labelledDone (MkLabelled { label = 1, inner = stuckComp Nil }) := Trivial

-- A field of a record literal.
type Holder = { inner: Effect.Comp Effect.NoOp Effect.NoRes Nat }

def holderDone (holder: Holder): Prop := IsDone holder.inner

theorem recordDone: holderDone { inner = Done 3 } := Trivial
theorem recordComputes: holderDone { inner = stuckComp Nil } := Trivial

-- An argument given by name.
def takes (count: Nat) (computation: Effect.Comp Effect.NoOp Effect.NoRes Nat): Prop := IsDone computation

theorem namedArgumentDone: takes (computation := Done 3) (count := 1) := Trivial
theorem namedArgumentComputes: takes (computation := stuckComp Nil) (count := 1) := Trivial

-- Items of a list and parts of a tuple.
theorem listDone: allDone [Done 3, Done 4] := Both Trivial (Both Trivial Trivial)
theorem listComputes: allDone [stuckComp Nil] := Both Trivial Trivial
theorem tupleDone: pairDone (1, Done 3) := Trivial
theorem tupleComputes: pairDone (1, stuckComp Nil) := Trivial

-- Through a function that takes and returns a computation.
theorem identityDone: IsDone (identityComp (Done 3)) := Trivial
theorem identityComputes: IsDone (identityComp (stuckComp Nil)) := Trivial
theorem bodyDone: IsDone (passOn (Done 3)) := Trivial

-- A written `Done` is a computation where one is expected, so `runPure` takes
-- it (it was refused while the argument was run in place).
theorem runIdentity (n: Nat): Effect.runPure (identityComp (Done n)) = n := rfl

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

-- Dot notation on a call whose declared result is the nickname: the
-- nickname's namespace is tried first, and the computation is passed, not run.
def stuckThunk: List Nat -> Thunk
  | Nil => 0
  | Cons x xs => 1

def finishedOfCall (xs: List Nat): Prop := (stuckThunk xs).finished

-- The same for a nickname of an ordinary type.
def Meters: Type := Nat

def Meters.double (m: Meters): Meters := m + m

def meters (n: Nat): Meters := n

def doubled (n: Nat): Meters := (meters n).double

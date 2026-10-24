-- An operand of `=`, and a branch of an `if` or `match` checked against a
-- computation type written as one, is passed as written rather than run
-- (D1140 (a), docs/proposals/effect-polymorphism.md). Before, a computation
-- there was run in place and re-wrapped: `if b then c else d` against
-- `Comp NoOp NoRes Nat` was `Done (if b then runPure c else runPure d)`, and
-- the `c` of `Effect.bind c Done = c` was `Done (runPure c)`. The matching
-- `reject/effect-pass-branch.sw` and `reject/effect-pass-equation.sw` check
-- that an arbitrary computation isn't known to be `Done` there.
import Std (Effect, Eq, Bool, Abort)
import Std.Effect.Comp (Done, Call)

def IsDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Prop
  | Done value => Unit
  | Call () rest

-- `=` between computations at the concrete empty row: `bindDone`, stated at
-- a general row in `Effect/Laws.sw`, proves it as it is.
theorem bindDoneHere [a: Type] (computation: Effect.Comp Effect.NoOp Effect.NoRes a):
    Effect.bind computation Done = computation :=
  Effect.bindDone computation

theorem sameComputation [a: Type] (computation: Effect.Comp Effect.NoOp Effect.NoRes a): computation = computation := rfl

-- Over a row with abilities: the two calls are computations, compared as
-- they are (this was `E-ABILITY`, since each was run).
theorem sameCall (thunk: () -> {Abort} Nat): thunk () = thunk () := rfl

-- Branches checked against a written computation type.
def pick (choice: Bool) (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat :=
  if choice then first else second

theorem pickTrue (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): pick True first second = first := rfl
theorem pickFalse (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): pick False first second = second := rfl
theorem pickDone (second: Effect.Comp Effect.NoOp Effect.NoRes Nat): IsDone (pick True (Done 3) second) := Trivial

def choose (choice: Bool) (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat :=
  match choice with
    | True => first
    | False => second

theorem chooseTrue (first second: Effect.Comp Effect.NoOp Effect.NoRes Nat): choose True first second = first := rfl

-- After a `let`, and with a plain value in one branch (`Done 0`).
def pickOrZero (choice: Bool) (first: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat :=
  let zero := 0
  if choice then first else zero

theorem pickOrZeroTrue (first: Effect.Comp Effect.NoOp Effect.NoRes Nat): pickOrZero True first = first := rfl
theorem pickOrZeroFalse (first: Effect.Comp Effect.NoOp Effect.NoRes Nat): IsDone (pickOrZero False first) := Trivial

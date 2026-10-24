-- expect-error: E-REFL
-- The receiver is a call whose declared result type is the nickname `Thunk`.
-- Dot notation finds `Thunk.finished` through the nickname and passes the
-- computation as it is, so an arbitrary one isn't known to be `Done`
-- (see reject/effect-pass-dot.sw for a variable receiver).
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest

def Thunk: Type := Effect.Comp Effect.NoOp Effect.NoRes Nat

def Thunk.finished (computation: Thunk): Bool := isDone computation

def stuckThunk: List Nat -> Thunk
  | Nil => 0
  | Cons x xs => 1

theorem anyIsDone: (xs: List Nat) -> (stuckThunk xs).finished = True := xs => rfl

-- Abilities as data (docs/proposals/abilities.md), written by hand: there's
-- no `ability` or `handle` syntax yet. A computation is a `Comp` tree from
-- the prelude, and a deep handler is a structurally recursive function over
-- it, checked like any other.

import Std.Effect (Comp, Plus, PlusRes, bind, foldComp)
import Std (List)

type Unit1: Type =
  | MkUnit

type Empty: Type

def fromEmpty: Empty -> a
  | ()

-- Signatures

-- `State Nat`: `get` returns the state, `put` replaces it.
type StateOp: Type =
  | Get
  | Put (n: Nat)

def StateRes: StateOp -> Type
  | Get => Nat
  | Put n => Unit1

-- `Choose`: a yes/no choice.
type ChooseOp: Type =
  | Choose

def ChooseRes: ChooseOp -> Type
  | Choose => Bool

-- `Abort`: stop. It returns `Empty`, so nothing can continue.
type AbortOp: Type =
  | Abort

def AbortRes: AbortOp -> Type
  | Abort => Empty

-- Two signatures side by side, `{l, r}`, use the prelude's `Plus` and `PlusRes`.

-- Computations with the row `{State Nat, Choose}`.
def SC (a: Type): Type := Comp (Plus StateOp ChooseOp) (PlusRes StateRes ChooseRes) a

type FnStateOp: Type =
  | GetFn
  | PutFn (f: Nat -> Comp ChooseOp ChooseRes Nat)

def FnStateRes: FnStateOp -> Type
  | GetFn => Nat -> Comp ChooseOp ChooseRes Nat
  | PutFn f => Unit1

-- A computation type whose operations come from a type function stuck on a
-- variable: not a row of abilities, so it's an ordinary data type here.
def OpsOf: Bool -> Type
  | True => ChooseOp
  | False => AbortOp

def ResOf: (b: Bool) -> OpsOf b -> Type
  | True, o => ChooseRes o
  | False, o => AbortRes o

def eqPairs: List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
  | Nil, Nil => True
  | Cons (MkPair a b) xs, Cons (MkPair c d) ys =>
    if a == c then (if b == d then eqPairs xs ys else False) else False
  | _, _ => False

def eqNats: List Nat -> List Nat -> Bool
  | Nil, Nil => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _, _ => False

def fstOf: Pair a b -> a
  | MkPair x y => x

def sndOf: Pair a b -> b
  | MkPair x y => y

def isNone: Option a -> Bool
  | None => True
  | Some x => False

def fromSome0: Option Nat -> Nat
  | None => 0
  | Some x => x

-- A program can't take a computation apart (docs/proposals/proof-reification.md,
-- stage R2), so the hand-written handlers are local definitions of a theorem,
-- and each behaviour is a `let` that `rfl` checks.
theorem handlersBehave: Unit :=
  -- Handlers that remove the only ability
  def runState (s: Nat): Comp StateOp StateRes a -> Pair a Nat
    | Done x => MkPair x s
    | Call Get rest => runState s (rest s)
    | Call (Put n) rest => runState n (rest MkUnit)

  -- Resumes twice: every outcome, `True` first.
  def allResults: Comp ChooseOp ChooseRes a -> List a
    | Done x => [x]
    | Call Choose rest => List.append (allResults (rest True)) (allResults (rest False))

  -- Never resumes.
  def toOption: Comp AbortOp AbortRes a -> Option a
    | Done x => Some x
    | Call Abort rest => None

  -- Handlers for one ability in a row of two. Operations they don't handle are
  -- forwarded, with the handler wrapped round the rest (deep handlers).
  def runStateL [e: Type] [eres: e -> Type] [a: Type]
      (s: Nat): Comp (Plus StateOp e) (PlusRes StateRes eres) a -> Comp e eres (Pair a Nat)
    | Done x => Done (MkPair x s)
    | Call (L Get) rest => runStateL s (rest s)
    | Call (L (Put n)) rest => runStateL n (rest MkUnit)
    | Call (R o) rest => Call o (y => runStateL s (rest y))

  def allResultsR: [e: Type] -> [eres: e -> Type] -> [a: Type] ->
      Comp (Plus e ChooseOp) (PlusRes eres ChooseRes) a -> Comp e eres (List a)
    | Done x => Done [x]
    | Call (R Choose) rest =>
      bind (allResultsR (rest True)) (xs =>
        bind (allResultsR (rest False)) (ys => Done (List.append xs ys)))
    | Call (L o) rest => Call o (y => allResultsR (rest y))

  -- Handler order (from the review)

  -- p() =
  --   let b := choose()
  --   if b then put 1 else ()
  --   get()
  def get: SC Nat := Call (L Get) (n => Done n)

  def put (n: Nat): SC Unit1 := Call (L (Put n)) (u => Done u)

  def choose: SC Bool := Call (R Choose) (b => Done b)

  def p: SC Nat :=
    bind choose (b =>
      bind (if b then put 1 else Done MkUnit) (u =>
        get))

  -- State inside, choice outside: each branch has its own state.
  let stateInside: List (Pair Nat Nat) := allResults (runStateL 0 p)
  let stateInsideChoice: eqPairs stateInside [MkPair 1 1, MkPair 0 0] = True := rfl

  -- Choice inside, state outside: one state threads through both branches.
  let choiceInside: Pair (List Nat) Nat := runState 0 (allResultsR p)
  let choiceInsideState: (if eqNats (fstOf choiceInside) [1, 1] then sndOf choiceInside == 1 else False) = True := rfl

  -- A clause performing the ability it handles: its `get` goes to the *next*
  -- State handler out, so the handler's own result still has State.
  def scaleGets: Comp StateOp StateRes a -> Comp StateOp StateRes a
    | Done x => Done x
    | Call Get rest => Call Get (m => scaleGets (rest (m * 10)))
    | Call (Put n) rest => Call (Put n) (u => scaleGets (rest u))

  -- get() + 1
  def getPlusOne: Comp StateOp StateRes Nat := Call Get (n => Done (n + 1))

  let clauseGet: fstOf (runState 5 (scaleGets getPlusOne)) = 51 := rfl

  -- Abort: the polymorphic `abort` is the primitive one (returning `Empty`)
  -- followed by `fromEmpty`.
  def abort: Comp AbortOp AbortRes a := Call Abort (v => fromEmpty v)

  def safeDiv (n: Nat) (d: Nat): Comp AbortOp AbortRes Nat := if h: d != 0 then Done (n / d) else abort

  let abortStops: isNone (toOption (safeDiv 7 0)) = True := rfl
  let noAbort: fromSome0 (toOption (bind (safeDiv 7 2) (q => safeDiv 100 q))) = 33 := rfl

  -- The generic fold: `allResults` again, written with `foldComp`.
  def both: (o: ChooseOp) -> (ChooseRes o -> List a) -> List a
    | Choose, k => List.append (k True) (k False)

  def allResultsFold (c: Comp ChooseOp ChooseRes a): List a := foldComp (x => [x]) both c

  -- Three choices: eight outcomes.
  def threeChoices: Comp ChooseOp ChooseRes Nat :=
    Call Choose (a => Call Choose (b => Call Choose (c =>
      Done ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)))))

  let foldOutcomes: eqNats (allResultsFold threeChoices) [7, 6, 5, 4, 3, 2, 1, 0] = True := rfl
  let foldAgrees: eqNats (allResultsFold threeChoices) (allResults threeChoices) = True := rfl

  -- State holding functions is fine, pure or effectful, as long as the
  -- effects don't refer back to the state's own signature.
  def runFnState (f: Nat -> Comp ChooseOp ChooseRes Nat): Comp FnStateOp FnStateRes a -> a
    | Done x => x
    | Call GetFn rest => runFnState f (rest f)
    | Call (PutFn g) rest => runFnState g (rest MkUnit)

  -- Store "add 0 or 10", then read it back and run it under `allResults`.
  def storeAndRun: Comp FnStateOp FnStateRes (List Nat) :=
    Call (PutFn (n => Call Choose (b => Done (if b then n + 10 else n)))) (u =>
      Call GetFn (g => Done (allResults (g 5))))

  let effectfulFunctionInState: eqNats (runFnState (n => Done n) storeAndRun) [15, 5] = True := rfl

  def doneAnyway (b: Bool): Comp (OpsOf b) (ResOf b) Nat := Done 7

  def valueOr0: [o: Type] -> [r: o -> Type] -> Comp o r Nat -> Nat
    | Done x => x
    | Call c rest => 0

  let stuckOperationType: valueOr0 (doneAnyway True) = 7 := rfl
  Trivial

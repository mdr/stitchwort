-- Abilities as data (docs/proposals/abilities.md), written by hand: there's
-- no `ability` or `handle` syntax yet. A computation is a `Comp` tree from
-- the prelude, and a deep handler is a structurally recursive function over
-- it, checked like any other.

import Effect (Comp, Plus, PlusRes, bind, foldComp)

type Unit1 : Type =
  | MkUnit

type Empty : Type

def fromEmpty : Empty -> a
  | ()

-- Signatures

-- `State Nat`: `get` returns the state, `put` replaces it.
type StateOp : Type =
  | Get
  | Put (n : Nat)

def StateRes : StateOp -> Type
  | Get   => Nat
  | Put n => Unit1

-- `Choose`: a yes/no choice.
type ChooseOp : Type =
  | Choose

def ChooseRes : ChooseOp -> Type
  | Choose => Bool

-- `Abort`: stop. It returns `Empty`, so nothing can continue.
type AbortOp : Type =
  | Abort

def AbortRes : AbortOp -> Type
  | Abort => Empty

-- Two signatures side by side, `{l, r}`, use the prelude's `Plus` and `PlusRes`.

-- Handlers that remove the only ability

def runState (s : Nat) : Comp StateOp StateRes a -> Pair a Nat
  | Done x            => MkPair x s
  | Call Get rest     => runState s (rest s)
  | Call (Put n) rest => runState n (rest MkUnit)

-- Resumes twice: every outcome, `True` first.
def allResults : Comp ChooseOp ChooseRes a -> List a
  | Done x           => [x]
  | Call Choose rest => List.append (allResults (rest True)) (allResults (rest False))

-- Never resumes.
def toMaybe : Comp AbortOp AbortRes a -> Maybe a
  | Done x          => Just x
  | Call Abort rest => Nothing

-- Handlers for one ability in a row of two. Operations they don't handle are
-- forwarded, with the handler wrapped round the rest (deep handlers).

def runStateL [e : Type] [eres : e -> Type] [a : Type]
    (s : Nat) : Comp (Plus StateOp e) (PlusRes StateRes eres) a -> Comp e eres (Pair a Nat)
  | Done x                => Done (MkPair x s)
  | Call (L Get) rest     => runStateL s (rest s)
  | Call (L (Put n)) rest => runStateL n (rest MkUnit)
  | Call (R o) rest       => Call o (\y => runStateL s (rest y))

def allResultsR : [e : Type] -> [eres : e -> Type] -> [a : Type] ->
    Comp (Plus e ChooseOp) (PlusRes eres ChooseRes) a -> Comp e eres (List a)
  | Done x               => Done [x]
  | Call (R Choose) rest =>
    bind (allResultsR (rest True)) (\xs =>
      bind (allResultsR (rest False)) (\ys => Done (List.append xs ys)))
  | Call (L o) rest      => Call o (\y => allResultsR (rest y))

-- Handler order (from the review)

-- p () =
--   let b := choose ()
--   if b then put 1 else ()
--   get ()
-- Computations with the row `{State Nat, Choose}`, and its operations.
def SC (a : Type) : Type := Comp (Plus StateOp ChooseOp) (PlusRes StateRes ChooseRes) a

def get : SC Nat := Call (L Get) (\n => Done n)

def put (n : Nat) : SC Unit1 := Call (L (Put n)) (\u => Done u)

def choose : SC Bool := Call (R Choose) (\b => Done b)

def p : SC Nat :=
  bind choose (\b =>
    bind (if b then put 1 else Done MkUnit) (\u =>
      get))

def eqPairs : List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
  | Nil,                  Nil                  => True
  | Cons (MkPair a b) xs, Cons (MkPair c d) ys =>
    if a == c then (if b == d then eqPairs xs ys else False) else False
  | _,                    _                    => False

def eqNats : List Nat -> List Nat -> Bool
  | Nil,       Nil       => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _,         _         => False

-- State inside, choice outside: each branch has its own state.
def stateInside : List (Pair Nat Nat) := allResults (runStateL 0 p)

test "state inside choice: each branch has its own state" :=
  eqPairs stateInside [MkPair 1 1, MkPair 0 0]

-- Choice inside, state outside: one state threads through both branches.
def choiceInside : Pair (List Nat) Nat := runState 0 (allResultsR p)

def fstOf : Pair a b -> a
  | MkPair x y => x

def sndOf : Pair a b -> b
  | MkPair x y => y

test "choice inside state: the state threads through" :=
  if eqNats (fstOf choiceInside) [1, 1] then sndOf choiceInside == 1 else False

-- A clause performing the ability it handles: its `get` goes to the *next*
-- State handler out, so the handler's own result still has State.
def scaleGets : Comp StateOp StateRes a -> Comp StateOp StateRes a
  | Done x            => Done x
  | Call Get rest     => Call Get (\m => scaleGets (rest (m * 10)))
  | Call (Put n) rest => Call (Put n) (\u => scaleGets (rest u))

-- get () + 1
def getPlusOne : Comp StateOp StateRes Nat := Call Get (\n => Done (n + 1))

test "a clause's own get goes to the outer handler" :=
  fstOf (runState 5 (scaleGets getPlusOne)) == 51

-- Abort: the polymorphic `abort` is the primitive one (returning `Empty`)
-- followed by `fromEmpty`.
def abort : Comp AbortOp AbortRes a := Call Abort (\v => fromEmpty v)

def safeDiv (n : Nat) (d : Nat) : Comp AbortOp AbortRes Nat := if h : d != 0 then Done (n / d) else abort

def isNothing : Maybe a -> Bool
  | Nothing => True
  | Just x  => False

def fromJust0 : Maybe Nat -> Nat
  | Nothing => 0
  | Just x  => x

test "abort stops" := isNothing (toMaybe (safeDiv 7 0))
test "no abort" := fromJust0 (toMaybe (bind (safeDiv 7 2) (\q => safeDiv 100 q))) == 33

-- The generic fold: `allResults` again, written with `foldComp`.
def both : (o : ChooseOp) -> (ChooseRes o -> List a) -> List a
  | Choose, k => List.append (k True) (k False)

def allResultsFold (c : Comp ChooseOp ChooseRes a) : List a := foldComp (\x => [x]) both c

-- Three choices: eight outcomes.
def threeChoices : Comp ChooseOp ChooseRes Nat :=
  Call Choose (\a => Call Choose (\b => Call Choose (\c =>
    Done ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)))))

test "fold" := eqNats (allResultsFold threeChoices) [7, 6, 5, 4, 3, 2, 1, 0]
test "fold agrees with the handler" :=
  eqNats (allResultsFold threeChoices) (allResults threeChoices)

-- State holding functions is fine, pure or effectful, as long as the
-- effects don't refer back to the state's own signature.
type FnStateOp : Type =
  | GetFn
  | PutFn (f : Nat -> Comp ChooseOp ChooseRes Nat)

def FnStateRes : FnStateOp -> Type
  | GetFn   => Nat -> Comp ChooseOp ChooseRes Nat
  | PutFn f => Unit1

def runFnState (f : Nat -> Comp ChooseOp ChooseRes Nat) : Comp FnStateOp FnStateRes a -> a
  | Done x              => x
  | Call GetFn rest     => runFnState f (rest f)
  | Call (PutFn g) rest => runFnState g (rest MkUnit)

-- Store "add 0 or 10", then read it back and run it under `allResults`.
def storeAndRun : Comp FnStateOp FnStateRes (List Nat) :=
  Call (PutFn (\n => Call Choose (\b => Done (if b then n + 10 else n)))) (\u =>
    Call GetFn (\g => Done (allResults (g 5))))

test "effectful function in state" :=
  eqNats (runFnState (\n => Done n) storeAndRun) [15, 5]

-- A computation type whose operations come from a type function stuck on a
-- variable: not a row of abilities, so it's an ordinary data type here.
def OpsOf : Bool -> Type
  | True  => ChooseOp
  | False => AbortOp

def ResOf : (b : Bool) -> OpsOf b -> Type
  | True,  o => ChooseRes o
  | False, o => AbortRes o

def doneAnyway (b : Bool) : Comp (OpsOf b) (ResOf b) Nat := Done 7

def valueOr0 : [o : Type] -> [r : o -> Type] -> Comp o r Nat -> Nat
  | Done x      => x
  | Call c rest => 0

test "a stuck operation type isn't a row" := valueOr0 (doneAnyway True) == 7

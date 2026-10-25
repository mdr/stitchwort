-- Rows as explicit mappings between signatures (docs/proposals/abilities.md,
-- "Rows"), written by hand with the prelude's `Plus`, `SigMap` and
-- `translate`. The elaborator will generate these. Tests compare operation
-- traces as well as results, since a mapping that dropped, repeated or
-- reordered an operation could still produce a well-typed result.

import Std.Effect (Comp, Plus, PlusRes, SigMap, bind, sigCompose, sigId, sigLeft, sigRight, sigSwap, translate)
import Std (List)

type Unit1: Type =
  | MkUnit

type Empty: Type

def fstOf: Pair a b → a
  | MkPair x y => x

def sndOf: Pair a b → b
  | MkPair x y => y

def eqNats: List Nat → List Nat → Bool
  | Nil, Nil => True
  | Cons x xs, Cons y ys => if x == y then eqNats xs ys else False
  | _, _ => False

def eqPairs: List (Pair Nat Nat) → List (Pair Nat Nat) → Bool
  | Nil, Nil => True
  | Cons (MkPair a b) xs, Cons (MkPair c d) ys =>
    if a == c then (if b == d then eqPairs xs ys else False) else False
  | _, _ => False

-- Signatures

type StateOp: Type =
  | Get
  | Put (n: Nat)

def StateRes: StateOp → Type
  | Get => Nat
  | Put n => Unit1

type ChooseOp: Type =
  | Choose

def ChooseRes: ChooseOp → Type
  | Choose => Bool

type TickOp: Type =
  | Tick

def TickRes: TickOp → Type
  | Tick => Unit1

type AbortOp: Type =
  | Abort

def AbortRes: AbortOp → Type
  | Abort => Empty

-- Answers for the traces: `get` gives 7 (recorded as 1), `put n` is recorded
-- as 100 + n, `choose` gives `True` (recorded as 2), and `tick` is recorded
-- as 3.
def answerState: (o: StateOp) → Pair Nat (StateRes o)
  | Get => MkPair 1 7
  | Put n => MkPair (100 + n) MkUnit

def answerChoose: (o: ChooseOp) → Pair Nat (ChooseRes o)
  | Choose => MkPair 2 True

def answerTick: (o: TickOp) → Pair Nat (TickRes o)
  | Tick => MkPair 3 MkUnit

def answerPlus [l r: Type] [lres: l → Type] [rres: r → Type]
    (al: (o: l) → Pair Nat (lres o)) (ar: (o: r) → Pair Nat (rres o)):
    (o: Plus l r) → Pair Nat (PlusRes lres rres o)
  | L o => al o
  | R o => ar o

-- A program in the row `{State, Choose}`
def SC (a: Type): Type := Comp (Plus StateOp ChooseOp) (PlusRes StateRes ChooseRes) a

def answerSC (o: Plus StateOp ChooseOp): Pair Nat (PlusRes StateRes ChooseRes o) := answerPlus answerState answerChoose o

def answerCS (o: Plus ChooseOp StateOp): Pair Nat (PlusRes ChooseRes StateRes o) := answerPlus answerChoose answerState o

-- Weakening `{Choose}` into `{{State, Choose}, Tick}` in two steps, and in one.
def SCT: Type := Plus (Plus StateOp ChooseOp) TickOp

def SCTRes (o: SCT): Type := PlusRes (PlusRes StateRes ChooseRes) TickRes o

def twoSteps: SigMap ChooseOp ChooseRes SCT SCTRes := sigCompose sigRight sigLeft

def oneStep: SigMap ChooseOp ChooseRes SCT SCTRes := MkSigMap (o => L (R o)) (o x => x)

def answerSCT (o: SCT): Pair Nat (SCTRes o) := answerPlus answerSC answerTick o

-- The same program weakened into `{State, {Choose, Abort}}`, so `runStateL`
-- runs with `e = Plus ChooseOp AbortOp`, and `allResultsL` with `e = Abort`.
def SCA: Type := Plus StateOp (Plus ChooseOp AbortOp)

def SCARes (o: SCA): Type := PlusRes StateRes (PlusRes ChooseRes AbortRes) o

def intoSCA: Plus StateOp ChooseOp → SCA
  | L o => L o
  | R o => R (L o)

def replySCA: (o: Plus StateOp ChooseOp) → SCARes (intoSCA o) → PlusRes StateRes ChooseRes o
  | L o, x => x
  | R o, x => x

def fromSomeNil: Option (List a) → List a
  | None => Nil
  | Some xs => xs

-- A program can't take a computation apart (docs/proposals/proof-reification.md,
-- stage R2), so the hand-written handlers and programs are local definitions
-- of a theorem, and each behaviour is a `let` that `rfl` checks.
theorem rowsBehave: Unit :=
  -- Traces

  -- Runs a computation with fixed answers, recording a number for each
  -- operation and then 1000 + the result. `answer` gives both the number to
  -- record and the response.
  def trace [op: Type] [res: op → Type]
      (answer: (o: op) → Pair Nat (res o)): Comp op res Nat → List Nat
    | Done x => [1000 + x]
    | Call o rest => Cons (fstOf (answer o)) (trace answer (rest (sndOf (answer o))))

  def get: SC Nat := Call (L Get) (n => Done n)

  def put (n: Nat): SC Unit1 := Call (L (Put n)) (u => Done u)

  def choose: SC Bool := Call (R Choose) (b => Done b)

  -- choose, then put 1 if it said yes, then get
  def p: SC Nat := bind choose (b => bind (if b then put 1 else Done MkUnit) (u => get))

  let theTrace: eqNats (trace answerSC p) [2, 101, 1, 1007] = True := rfl

  -- Mappings preserve traces

  let identity: eqNats (trace answerSC (translate sigId p)) (trace answerSC p) = True := rfl

  let swap: eqNats (trace answerCS (translate sigSwap p)) (trace answerSC p) = True := rfl

  let swapBack:
    eqNats (trace answerSC (translate sigSwap (translate sigSwap p))) (trace answerSC p) = True := rfl

  def chooseOnly: Comp ChooseOp ChooseRes Nat := Call Choose (b => Done (if b then 1 else 0))

  let composedWeakenings:
    eqNats (trace answerSCT (translate twoSteps chooseOnly)) (trace answerSCT (translate oneStep chooseOnly)) = True := rfl

  let weakeningKeepsTrace:
    eqNats (trace answerSCT (translate twoSteps chooseOnly)) (trace answerChoose chooseOnly) = True := rfl

  -- Handlers over an abstract rest of the row

  -- `State` on the left of any row `e`.
  def runStateL [e: Type] [eres: e → Type] [a: Type]
      (s: Nat): Comp (Plus StateOp e) (PlusRes StateRes eres) a → Comp e eres (Pair a Nat)
    | Done x => Done (MkPair x s)
    | Call (L Get) rest => runStateL s (rest s)
    | Call (L (Put n)) rest => runStateL n (rest MkUnit)
    | Call (R o) rest => Call o (y => runStateL s (rest y))

  -- `Choose` on the left of any row `e`: every outcome, `True` first.
  def allResultsL: [e: Type] → [eres: e → Type] → [a: Type] →
      Comp (Plus ChooseOp e) (PlusRes ChooseRes eres) a → Comp e eres (List a)
    | Done x => Done [x]
    | Call (L Choose) rest =>
      bind (allResultsL (rest True)) (xs =>
        bind (allResultsL (rest False)) (ys => Done (List.append xs ys)))
    | Call (R o) rest => Call o (y => allResultsL (rest y))

  -- Removing the last ability.
  def allResults: Comp ChooseOp ChooseRes a → List a
    | Done x => [x]
    | Call Choose rest => List.append (allResults (rest True)) (allResults (rest False))

  def runState (s: Nat): Comp StateOp StateRes a → Pair a Nat
    | Done x => MkPair x s
    | Call Get rest => runState s (rest s)
    | Call (Put n) rest => runState n (rest MkUnit)

  def toOption: Comp AbortOp AbortRes a → Option a
    | Done x => Some x
    | Call Abort rest => None

  -- `runStateL` with `e = Choose`.
  let stateThenChoice: List (Pair Nat Nat) := allResults (runStateL 0 p)

  let stateInsideChoice: eqPairs stateThenChoice [MkPair 1 1, MkPair 0 0] = True := rfl

  def pWider: Comp SCA SCARes Nat := translate (MkSigMap intoSCA replySCA) p

  let widerRest:
    eqPairs (fromSomeNil (toOption (allResultsL (runStateL 0 pWider)))) stateThenChoice = True := rfl

  -- Handling `Choose` when it's on the left instead: swap the program, then
  -- use `allResultsL` with `e = State`. Choice inside, state outside.
  let otherPosition:
    eqNats (fstOf (runState 0 (allResultsL (translate sigSwap p)))) [1, 1] = True := rfl
  Trivial

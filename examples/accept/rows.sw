-- Rows as explicit mappings between signatures (docs/proposals/abilities.md,
-- "Rows"), written by hand with the prelude's `Plus`, `SigMap` and
-- `translate`. The elaborator will generate these. Tests compare operation
-- traces as well as results, since a mapping that dropped, repeated or
-- reordered an operation could still produce a well-typed result.

type Unit1 : Type =
  | MkUnit

type Empty : Type

type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

type Maybe (a : Type) : Type =
  | Nothing
  | Just (x : a)

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

eqPairs : List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
eqPairs Nil                    Nil                    = True
eqPairs (Cons (MkPair a b) xs) (Cons (MkPair c d) ys) =
  if a == c then (if b == d then eqPairs xs ys else False) else False
eqPairs _                      _                      = False

-- Signatures

type StateOp : Type =
  | Get
  | Put (n : Nat)

StateRes : StateOp -> Type
StateRes Get     = Nat
StateRes (Put n) = Unit1

type ChooseOp : Type =
  | Choose

ChooseRes : ChooseOp -> Type
ChooseRes Choose = Bool

type TickOp : Type =
  | Tick

TickRes : TickOp -> Type
TickRes Tick = Unit1

type AbortOp : Type =
  | Abort

AbortRes : AbortOp -> Type
AbortRes Abort = Empty

-- Traces

-- Runs a computation with fixed answers, recording a number for each
-- operation and then 1000 + the result. `answer` gives both the number to
-- record and the response.
trace : [op : Type] -> [res : op -> Type] ->
  ((o : op) -> Pair Nat (res o)) -> Comp op res Nat -> List Nat
trace answer (Done x)      = [1000 + x]
trace answer (Call o rest) = Cons (fstOf (answer o)) (trace answer (rest (sndOf (answer o))))

-- `get` gives 7 (recorded as 1), `put n` is recorded as 100 + n, `choose`
-- gives `True` (recorded as 2), and `tick` is recorded as 3.
answerState : (o : StateOp) -> Pair Nat (StateRes o)
answerState Get     = MkPair 1 7
answerState (Put n) = MkPair (100 + n) MkUnit

answerChoose : (o : ChooseOp) -> Pair Nat (ChooseRes o)
answerChoose Choose = MkPair 2 True

answerTick : (o : TickOp) -> Pair Nat (TickRes o)
answerTick Tick = MkPair 3 MkUnit

answerPlus : [l r : Type] -> [lres : l -> Type] -> [rres : r -> Type] ->
  ((o : l) -> Pair Nat (lres o)) -> ((o : r) -> Pair Nat (rres o)) ->
  (o : Plus l r) -> Pair Nat (PlusRes lres rres o)
answerPlus al ar (L o) = al o
answerPlus al ar (R o) = ar o

-- A program in the row `{State, Choose}`

SC : Type -> Type
SC a = Comp (Plus StateOp ChooseOp) (PlusRes StateRes ChooseRes) a

get : SC Nat
get = Call (L Get) (\n -> Done n)

put : Nat -> SC Unit1
put n = Call (L (Put n)) (\u -> Done u)

choose : SC Bool
choose = Call (R Choose) (\b -> Done b)

-- choose, then put 1 if it said yes, then get
p : SC Nat
p = bind choose (\b -> bind (if b then put 1 else Done MkUnit) (\u -> get))

answerSC : (o : Plus StateOp ChooseOp) -> Pair Nat (PlusRes StateRes ChooseRes o)
answerSC o = answerPlus answerState answerChoose o

answerCS : (o : Plus ChooseOp StateOp) -> Pair Nat (PlusRes ChooseRes StateRes o)
answerCS o = answerPlus answerChoose answerState o

test "the trace itself" = eqNats (trace answerSC p) [2, 101, 1, 1007]

-- Mappings preserve traces

test "identity" = eqNats (trace answerSC (translate sigId p)) (trace answerSC p)

test "swap" = eqNats (trace answerCS (translate sigSwap p)) (trace answerSC p)

test "swap, then swap back" =
  eqNats (trace answerSC (translate sigSwap (translate sigSwap p))) (trace answerSC p)

-- Weakening `{Choose}` into `{{State, Choose}, Tick}` in two steps, and in one.
chooseOnly : Comp ChooseOp ChooseRes Nat
chooseOnly = Call Choose (\b -> Done (if b then 1 else 0))

SCT : Type
SCT = Plus (Plus StateOp ChooseOp) TickOp

SCTRes : SCT -> Type
SCTRes o = PlusRes (PlusRes StateRes ChooseRes) TickRes o

twoSteps : SigMap ChooseOp ChooseRes SCT SCTRes
twoSteps = sigCompose sigRight sigLeft

oneStep : SigMap ChooseOp ChooseRes SCT SCTRes
oneStep = MkSigMap (\o -> L (R o)) (\o x -> x)

answerSCT : (o : SCT) -> Pair Nat (SCTRes o)
answerSCT o = answerPlus answerSC answerTick o

test "composed weakenings agree with the direct one" =
  eqNats (trace answerSCT (translate twoSteps chooseOnly)) (trace answerSCT (translate oneStep chooseOnly))

test "weakening keeps the trace" =
  eqNats (trace answerSCT (translate twoSteps chooseOnly)) (trace answerChoose chooseOnly)

-- Handlers over an abstract rest of the row

-- `State` on the left of any row `e`.
runStateL : [e : Type] -> [eres : e -> Type] -> [a : Type] ->
  Nat -> Comp (Plus StateOp e) (PlusRes StateRes eres) a -> Comp e eres (Pair a Nat)
runStateL s (Done x)                = Done (MkPair x s)
runStateL s (Call (L Get) rest)     = runStateL s (rest s)
runStateL s (Call (L (Put n)) rest) = runStateL n (rest MkUnit)
runStateL s (Call (R o) rest)       = Call o (\y -> runStateL s (rest y))

-- `Choose` on the left of any row `e`: every outcome, `True` first.
allResultsL : [e : Type] -> [eres : e -> Type] -> [a : Type] ->
  Comp (Plus ChooseOp e) (PlusRes ChooseRes eres) a -> Comp e eres (List a)
allResultsL (Done x)               = Done [x]
allResultsL (Call (L Choose) rest) =
  bind (allResultsL (rest True)) (\xs ->
    bind (allResultsL (rest False)) (\ys -> Done (append xs ys)))
allResultsL (Call (R o) rest)      = Call o (\y -> allResultsL (rest y))

-- Removing the last ability.
allResults : Comp ChooseOp ChooseRes a -> List a
allResults (Done x)           = [x]
allResults (Call Choose rest) = append (allResults (rest True)) (allResults (rest False))

runState : Nat -> Comp StateOp StateRes a -> Pair a Nat
runState s (Done x)            = MkPair x s
runState s (Call Get rest)     = runState s (rest s)
runState s (Call (Put n) rest) = runState n (rest MkUnit)

toMaybe : Comp AbortOp AbortRes a -> Maybe a
toMaybe (Done x)          = Just x
toMaybe (Call Abort rest) = Nothing

fromJustNil : Maybe (List a) -> List a
fromJustNil Nothing   = Nil
fromJustNil (Just xs) = xs

-- `runStateL` with `e = Choose`.
stateThenChoice : List (Pair Nat Nat)
stateThenChoice = allResults (runStateL 0 p)

test "state inside choice" = eqPairs stateThenChoice [MkPair 1 1, MkPair 0 0]

-- The same program weakened into `{State, {Choose, Abort}}`, so `runStateL`
-- runs with `e = Plus ChooseOp AbortOp`, and `allResultsL` with `e = Abort`.
SCA : Type
SCA = Plus StateOp (Plus ChooseOp AbortOp)

SCARes : SCA -> Type
SCARes o = PlusRes StateRes (PlusRes ChooseRes AbortRes) o

intoSCA : Plus StateOp ChooseOp -> SCA
intoSCA (L o) = L o
intoSCA (R o) = R (L o)

replySCA : (o : Plus StateOp ChooseOp) -> SCARes (intoSCA o) -> PlusRes StateRes ChooseRes o
replySCA (L o) x = x
replySCA (R o) x = x

pWider : Comp SCA SCARes Nat
pWider = translate (MkSigMap intoSCA replySCA) p

test "the same handler, with a wider rest of the row" =
  eqPairs (fromJustNil (toMaybe (allResultsL (runStateL 0 pWider)))) stateThenChoice

-- Handling `Choose` when it's on the left instead: swap the program, then
-- use `allResultsL` with `e = State`. Choice inside, state outside.
test "a handler for the other position" =
  eqNats (fstOf (runState 0 (allResultsL (translate sigSwap p)))) [1, 1]

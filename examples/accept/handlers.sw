-- Abilities as data (docs/proposals/abilities.md), written by hand: there's
-- no `ability` or `handle` syntax yet. A computation is a `Comp` tree from
-- the prelude, and a deep handler is a structurally recursive function over
-- it, checked like any other.

type Unit1 : Type =
  | MkUnit

type Empty : Type

fromEmpty : Empty -> a
fromEmpty ()

type Pair (a : Type) (b : Type) : Type =
  | MkPair (fst : a) (snd : b)

type Maybe (a : Type) : Type =
  | Nothing
  | Just (x : a)

-- Signatures

-- `State Nat`: `get` returns the state, `put` replaces it.
type StateOp : Type =
  | Get
  | Put (n : Nat)

StateRes : StateOp -> Type
StateRes Get     = Nat
StateRes (Put n) = Unit1

-- `Choose`: a yes/no choice.
type ChooseOp : Type =
  | Choose

ChooseRes : ChooseOp -> Type
ChooseRes Choose = Bool

-- `Abort`: stop. It returns `Empty`, so nothing can continue.
type AbortOp : Type =
  | Abort

AbortRes : AbortOp -> Type
AbortRes Abort = Empty

-- Two signatures side by side, `{l, r}`, use the prelude's `Plus` and `PlusRes`.

-- Handlers that remove the only ability

runState : Nat -> Comp StateOp StateRes a -> Pair a Nat
runState s (Done x)            = MkPair x s
runState s (Call Get rest)     = runState s (rest s)
runState s (Call (Put n) rest) = runState n (rest MkUnit)

-- Resumes twice: every outcome, `True` first.
allResults : Comp ChooseOp ChooseRes a -> List a
allResults (Done x)           = [x]
allResults (Call Choose rest) = append (allResults (rest True)) (allResults (rest False))

-- Never resumes.
toMaybe : Comp AbortOp AbortRes a -> Maybe a
toMaybe (Done x)          = Just x
toMaybe (Call Abort rest) = Nothing

-- Handlers for one ability in a row of two. Operations they don't handle are
-- forwarded, with the handler wrapped round the rest (deep handlers).

runStateL : [e : Type] -> [eres : e -> Type] -> [a : Type] ->
  Nat -> Comp (Plus StateOp e) (PlusRes StateRes eres) a -> Comp e eres (Pair a Nat)
runStateL s (Done x)                = Done (MkPair x s)
runStateL s (Call (L Get) rest)     = runStateL s (rest s)
runStateL s (Call (L (Put n)) rest) = runStateL n (rest MkUnit)
runStateL s (Call (R o) rest)       = Call o (\y -> runStateL s (rest y))

allResultsR : [e : Type] -> [eres : e -> Type] -> [a : Type] ->
  Comp (Plus e ChooseOp) (PlusRes eres ChooseRes) a -> Comp e eres (List a)
allResultsR (Done x)               = Done [x]
allResultsR (Call (R Choose) rest) =
  bind (allResultsR (rest True)) (\xs ->
    bind (allResultsR (rest False)) (\ys -> Done (append xs ys)))
allResultsR (Call (L o) rest)      = Call o (\y -> allResultsR (rest y))

-- Handler order (from the review)

-- p () =
--   let b = choose ()
--   if b then put 1 else ()
--   get ()
-- Computations with the row `{State Nat, Choose}`, and its operations.
SC : Type -> Type
SC a = Comp (Plus StateOp ChooseOp) (PlusRes StateRes ChooseRes) a

get : SC Nat
get = Call (L Get) (\n -> Done n)

put : Nat -> SC Unit1
put n = Call (L (Put n)) (\u -> Done u)

choose : SC Bool
choose = Call (R Choose) (\b -> Done b)

p : SC Nat
p =
  bind choose (\b ->
    bind (if b then put 1 else Done MkUnit) (\u ->
      get))

eqPairs : List (Pair Nat Nat) -> List (Pair Nat Nat) -> Bool
eqPairs Nil                       Nil                       = True
eqPairs (Cons (MkPair a b) xs)    (Cons (MkPair c d) ys)    =
  if a == c then (if b == d then eqPairs xs ys else False) else False
eqPairs _                         _                         = False

eqNats : List Nat -> List Nat -> Bool
eqNats Nil         Nil         = True
eqNats (Cons x xs) (Cons y ys) = if x == y then eqNats xs ys else False
eqNats _           _           = False

-- State inside, choice outside: each branch has its own state.
stateInside : List (Pair Nat Nat)
stateInside = allResults (runStateL 0 p)

test "state inside choice: each branch has its own state" =
  eqPairs stateInside [MkPair 1 1, MkPair 0 0]

-- Choice inside, state outside: one state threads through both branches.
choiceInside : Pair (List Nat) Nat
choiceInside = runState 0 (allResultsR p)

fstOf : Pair a b -> a
fstOf (MkPair x y) = x

sndOf : Pair a b -> b
sndOf (MkPair x y) = y

test "choice inside state: the state threads through" =
  if eqNats (fstOf choiceInside) [1, 1] then sndOf choiceInside == 1 else False

-- A clause performing the ability it handles: its `get` goes to the *next*
-- State handler out, so the handler's own result still has State.
scaleGets : Comp StateOp StateRes a -> Comp StateOp StateRes a
scaleGets (Done x)            = Done x
scaleGets (Call Get rest)     = Call Get (\m -> scaleGets (rest (m * 10)))
scaleGets (Call (Put n) rest) = Call (Put n) (\u -> scaleGets (rest u))

-- get () + 1
getPlusOne : Comp StateOp StateRes Nat
getPlusOne = Call Get (\n -> Done (n + 1))

test "a clause's own get goes to the outer handler" =
  fstOf (runState 5 (scaleGets getPlusOne)) == 51

-- Abort: the polymorphic `abort` is the primitive one (returning `Empty`)
-- followed by `fromEmpty`.
abort : Comp AbortOp AbortRes a
abort = Call Abort (\v -> fromEmpty v)

safeDiv : Nat -> Nat -> Comp AbortOp AbortRes Nat
safeDiv n d = if h : d != 0 then Done (n / d) else abort

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just x) = False

fromJust0 : Maybe Nat -> Nat
fromJust0 Nothing  = 0
fromJust0 (Just x) = x

test "abort stops" = isNothing (toMaybe (safeDiv 7 0))
test "no abort" = fromJust0 (toMaybe (bind (safeDiv 7 2) (\q -> safeDiv 100 q))) == 33

-- The generic fold: `allResults` again, written with `foldComp`.
both : (o : ChooseOp) -> (ChooseRes o -> List a) -> List a
both Choose k = append (k True) (k False)

allResultsFold : Comp ChooseOp ChooseRes a -> List a
allResultsFold c = foldComp (\x -> [x]) both c

-- Three choices: eight outcomes.
threeChoices : Comp ChooseOp ChooseRes Nat
threeChoices =
  Call Choose (\a -> Call Choose (\b -> Call Choose (\c ->
    Done ((if a then 4 else 0) + (if b then 2 else 0) + (if c then 1 else 0)))))

test "fold" = eqNats (allResultsFold threeChoices) [7, 6, 5, 4, 3, 2, 1, 0]
test "fold agrees with the handler" =
  eqNats (allResultsFold threeChoices) (allResults threeChoices)

-- State holding functions is fine, pure or effectful, as long as the
-- effects don't refer back to the state's own signature.
type FnStateOp : Type =
  | GetFn
  | PutFn (f : Nat -> Comp ChooseOp ChooseRes Nat)

FnStateRes : FnStateOp -> Type
FnStateRes GetFn     = Nat -> Comp ChooseOp ChooseRes Nat
FnStateRes (PutFn f) = Unit1

runFnState : (Nat -> Comp ChooseOp ChooseRes Nat) -> Comp FnStateOp FnStateRes a -> a
runFnState f (Done x)              = x
runFnState f (Call GetFn rest)     = runFnState f (rest f)
runFnState f (Call (PutFn g) rest) = runFnState g (rest MkUnit)

-- Store "add 0 or 10", then read it back and run it under `allResults`.
storeAndRun : Comp FnStateOp FnStateRes (List Nat)
storeAndRun =
  Call (PutFn (\n -> Call Choose (\b -> Done (if b then n + 10 else n)))) (\u ->
    Call GetFn (\g -> Done (allResults (g 5))))

test "effectful function in state" =
  eqNats (runFnState (\n -> Done n) storeAndRun) [15, 5]

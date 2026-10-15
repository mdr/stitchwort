-- The `IO` ability and `simulate` (docs/proposals/text-and-io.md, Part 2).
-- `simulate` is an ordinary handler from the prelude: it answers each
-- `readLine` from a list of scripted lines and records each `print`.

eqTexts : List Text -> List Text -> Bool
eqTexts Nil         Nil         = True
eqTexts (Cons x xs) (Cons y ys) = if x == y then eqTexts xs ys else False
eqTexts _           _           = False

-- What a simulated run printed, and its result.
printed : Pair (List Text) a -> List Text
printed r = fst r

result : Pair (List Text) a -> a
result r = snd r

isJustText : Text -> Maybe Text -> Bool
isJustText t Nothing  = False
isJustText t (Just u) = t == u

isNothing : Maybe a -> Bool
isNothing Nothing  = True
isNothing (Just x) = False

-- Printing

hello : () -> {IO} Nat
hello u =
  print "one"
  print "two"
  print "three"
  3

test "prints are recorded in order" =
  eqTexts (printed (simulate [] hello)) ["one", "two", "three"]

test "the result comes back too" = result (simulate [] hello) == 3

test "a payload with a newline is one entry" =
  eqTexts (printed (simulate [] (\u -> print "a\nb"))) ["a\nb"]

test "an empty payload is an entry" =
  eqTexts (printed (simulate [] (\u -> print ""))) [""]

-- Reading

test "an empty line is Just \"\"" =
  isJustText "" (result (simulate [""] (\u -> readLine ())))

test "a line is read whole" =
  isJustText "  two words  " (result (simulate ["  two words  "] (\u -> readLine ())))

test "no input: Nothing" = isNothing (result (simulate [] (\u -> readLine ())))

-- Reads three times from one line of input.
readThree : () -> {IO} (List (Maybe Text))
readThree u =
  let a = readLine ()
  let b = readLine ()
  let c = readLine ()
  [a, b, c]

maybesAre : List (Maybe Text) -> Bool
maybesAre (Cons a (Cons b (Cons c Nil))) =
  if isJustText "x" a then (if isNothing b then isNothing c else False) else False
maybesAre _ = False

test "end of input keeps giving Nothing" = maybesAre (result (simulate ["x"] readThree))

-- Only the lines asked for are used.
test "unread input is ignored" =
  isJustText "first" (result (simulate ["first", "second"] (\u -> readLine ())))

-- Reading and printing interleaved

-- Echoes each line until the input runs out, reading at most `n` lines. The
-- bound keeps the recursion structural.
echoLine : Maybe Text -> (() -> {IO} ()) -> {IO} ()
echoLine Nothing  more = ()
echoLine (Just l) more =
  print l
  more ()

echo : Nat -> {IO} ()
echo 0        = ()
echo (Succ n) = echoLine (readLine ()) (\u -> echo n)

test "echo" =
  eqTexts (printed (simulate ["a", "", "c"] (\u -> echo 10))) ["a", "", "c"]

test "echo stops at its bound" =
  eqTexts (printed (simulate ["a", "b", "c"] (\u -> echo 2))) ["a", "b"]

test "echo with no input prints nothing" =
  eqTexts (printed (simulate [] (\u -> echo 10))) []

-- Numbers each line, and returns how many there were.
numberLine : Nat -> Maybe Text -> (() -> {IO} Nat) -> {IO} Nat
numberLine i Nothing  more = i - 1
numberLine i (Just l) more =
  print (natToText i ++ ": " ++ l)
  more ()

numberFrom : Nat -> Nat -> {IO} Nat
numberFrom i 0        = i - 1
numberFrom i (Succ n) = numberLine i (readLine ()) (\u -> numberFrom (i + 1) n)

numbered : Pair (List Text) Nat
numbered = simulate ["apple", "banana", "cherry"] (\u -> numberFrom 1 100)

test "numbering lines" =
  eqTexts (printed numbered) ["1: apple", "2: banana", "3: cherry"]

test "numbering lines: the count" = result numbered == 3

-- A prompt, then a read, then a reply.
textOr : Text -> Maybe Text -> Text
textOr d Nothing  = d
textOr d (Just t) = t

greet : () -> {IO} ()
greet u =
  print "Name?"
  let name = readLine ()
  print ("Hello, " ++ textOr "stranger" name ++ "!")

test "prompt and reply" =
  eqTexts (printed (simulate ["Ada"] greet)) ["Name?", "Hello, Ada!"]

test "prompt and reply at end of input" =
  eqTexts (printed (simulate [] greet)) ["Name?", "Hello, stranger!"]

-- `IO` with other abilities

type Empty : Type

fromEmpty : Empty -> a
fromEmpty ()

ability State (s : Type) where
  get : () -> {State s} s
  put : s -> {State s} ()

ability Abort where
  abort : () -> {Abort} Empty

runState : s -> (() -> {State s | e} a) -> {e} Pair a s
runState init prog =
  let run : s -> {e} Pair a s =
    handle prog () with
      | return x       -> \st -> MkPair x st
      | get u => k     -> \st -> k st st
      | put st2 => k   -> \st -> k () st2
  run init

toMaybe : (() -> {Abort | e} a) -> {e} Maybe a
toMaybe prog =
  handle prog () with
    | return x      -> Just x
    | abort u => k  -> Nothing

-- Reads two lines, counting them in the state, and prints the count.
countIS : () -> {IO, State Nat} ()
countIS u =
  let a = readLine ()
  put (get () + 1)
  let b = readLine ()
  put (get () + 1)
  print (natToText (get ()))

-- The same, with the row the other way round.
countSI : () -> {State Nat, IO} ()
countSI u =
  let a = readLine ()
  put (get () + 1)
  let b = readLine ()
  put (get () + 1)
  print (natToText (get ()))

-- `simulate` outside, `runState` inside.
stateInside : (() -> {State Nat, IO} ()) -> Pair (List Text) Nat
stateInside prog =
  let r = simulate ["x", "y"] (\u -> runState 10 prog)
  MkPair (printed r) (snd (result r))

-- `runState` outside, `simulate` inside.
stateOutside : (() -> {State Nat, IO} ()) -> Pair (List Text) Nat
stateOutside prog =
  let r = runState 10 (\u -> simulate ["x", "y"] prog)
  MkPair (printed (fst r)) (snd r)

checkCount : Pair (List Text) Nat -> Bool
checkCount r = if eqTexts (fst r) ["12"] then snd r == 12 else False

test "IO then State, State handled inside"    = checkCount (stateInside countIS)
test "IO then State, State handled outside"   = checkCount (stateOutside countIS)
test "State then IO, State handled inside"    = checkCount (stateInside countSI)
test "State then IO, State handled outside"   = checkCount (stateOutside countSI)

-- Prints, then stops.
printThenAbort : () -> {IO, Abort} Nat
printThenAbort u =
  print "before"
  let e = abort ()
  print "after"
  fromEmpty e

abortThenPrint : () -> {Abort, IO} Nat
abortThenPrint u =
  print "before"
  let e = abort ()
  print "after"
  fromEmpty e

-- With `toMaybe` inside, what was printed before the abort is kept.
test "abort inside simulate keeps earlier prints" =
  let r = simulate [] (\u -> toMaybe printThenAbort)
  if eqTexts (printed r) ["before"] then isNothing (result r) else False

test "abort inside simulate, the other row order" =
  let r = simulate [] (\u -> toMaybe abortThenPrint)
  if eqTexts (printed r) ["before"] then isNothing (result r) else False

-- With `toMaybe` outside, the abort discards the whole simulated run.
test "abort outside simulate discards the run" =
  isNothing (toMaybe (\u -> simulate [] printThenAbort))

test "abort outside simulate, the other row order" =
  isNothing (toMaybe (\u -> simulate [] abortThenPrint))

-- A program with no `IO` at all

test "a pure program prints nothing" =
  let r = simulate ["unused"] (\u -> 6 * 7)
  if eqTexts (printed r) [] then result r == 42 else False

test "a program with only State" =
  let r = runState 1 (\u -> simulate [] (\v -> put (get () + 1)))
  if eqTexts (printed (fst r)) [] then snd r == 2 else False

-- A long run

printMany : Nat -> {IO} ()
printMany 0        = ()
printMany (Succ n) =
  print "x"
  printMany n

test "5,000 prints" = length (printed (simulate [] (\u -> printMany 5000))) == 5000

-- By computation

theorem greetOutput : printed (simulate ["Ada"] greet) = ["Name?", "Hello, Ada!"]
greetOutput = rfl

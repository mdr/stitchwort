-- The `IO` ability and `IO.simulate` (docs/proposals/text-and-io.md, Part 2).
-- `IO.simulate` is an ordinary handler from the prelude: it answers each
-- `IO.readLine` from a list of scripted lines and records each `IO.print`.

import Std (IO, List, Nat, Pair)

def eqTexts: List Text → List Text → Bool
  | Nil, Nil => True
  | Cons x xs, Cons y ys => if x == y then eqTexts xs ys else False
  | _, _ => False

-- What a simulated run printed, and its result.
def printed (r: Pair (List Text) a): List Text := Pair.fst r

def result (r: Pair (List Text) a): a := Pair.snd r

def isSomeText (t: Text): Option Text → Bool
  | None => False
  | Some u => t == u

def isNone: Option a → Bool
  | None => True
  | Some x => False

-- Printing

def hello(): {IO} Nat :=
  IO.print "one"
  IO.print "two"
  IO.print "three"
  3

test "prints are recorded in order" :=
  eqTexts (printed (IO.simulate [] hello)) ["one", "two", "three"]

test "the result comes back too" := result (IO.simulate [] hello) == 3

test "a payload with a newline is one entry" :=
  eqTexts (printed (IO.simulate [] (u => IO.print "a\nb"))) ["a\nb"]

test "an empty payload is an entry" :=
  eqTexts (printed (IO.simulate [] (u => IO.print ""))) [""]

-- Reading

test "an empty line is Some \"\"" :=
  isSomeText "" (result (IO.simulate [""] (u => IO.readLine())))

test "a line is read whole" :=
  isSomeText "  two words  " (result (IO.simulate ["  two words  "] (u => IO.readLine())))

test "no input: None" := isNone (result (IO.simulate [] (u => IO.readLine())))

-- Reads three times from one line of input.
def readThree(): {IO} (List (Option Text)) :=
  let a := IO.readLine()
  let b := IO.readLine()
  let c := IO.readLine()
  [a, b, c]

def maybesAre: List (Option Text) → Bool
  | Cons a (Cons b (Cons c Nil)) =>
    if isSomeText "x" a then (if isNone b then isNone c else False) else False
  | _ => False

test "end of input keeps giving None" := maybesAre (result (IO.simulate ["x"] readThree))

-- Only the lines asked for are used.
test "unread input is ignored" :=
  isSomeText "first" (result (IO.simulate ["first", "second"] (u => IO.readLine())))

-- Reading and printing interleaved

-- Echoes each line until the input runs out, reading at most `n` lines. The
-- bound keeps the recursion structural.
def echoLine: Option Text → (() → {IO} ()) → {IO} ()
  | None, more => ()
  | Some l, more =>
    IO.print l
    more()

def echo: Nat → {IO} ()
  | 0 => ()
  | Succ n => echoLine (IO.readLine()) (u => echo n)

test "echo" :=
  eqTexts (printed (IO.simulate ["a", "", "c"] (u => echo 10))) ["a", "", "c"]

test "echo stops at its bound" :=
  eqTexts (printed (IO.simulate ["a", "b", "c"] (u => echo 2))) ["a", "b"]

test "echo with no input prints nothing" :=
  eqTexts (printed (IO.simulate [] (u => echo 10))) []

-- Numbers each line, and returns how many there were.
def numberLine (i: Nat): Option Text → (() → {IO} Nat) → {IO} Nat
  | None, more => i - 1
  | Some l, more =>
    IO.print (Nat.toText i ++ ": " ++ l)
    more()

def numberFrom (i: Nat): Nat → {IO} Nat
  | 0 => i - 1
  | Succ n => numberLine i (IO.readLine()) (u => numberFrom (i + 1) n)

def numbered: Pair (List Text) Nat := IO.simulate ["apple", "banana", "cherry"] (u => numberFrom 1 100)

test "numbering lines" :=
  eqTexts (printed numbered) ["1: apple", "2: banana", "3: cherry"]

test "numbering lines: the count" := result numbered == 3

-- A prompt, then a read, then a reply.
def textOr (d: Text): Option Text → Text
  | None => d
  | Some t => t

def greet(): {IO} () :=
  IO.print "Name?"
  let name := IO.readLine()
  IO.print ("Hello, " ++ textOr "stranger" name ++ "!")

test "prompt and reply" :=
  eqTexts (printed (IO.simulate ["Ada"] greet)) ["Name?", "Hello, Ada!"]

test "prompt and reply at end of input" :=
  eqTexts (printed (IO.simulate [] greet)) ["Name?", "Hello, stranger!"]

-- `IO` with other abilities

type Empty: Type

def fromEmpty: Empty → a
  | ()

ability State (s: Type) where
  get: () → {State s} s
  put: s → {State s} ()

ability Abort where
  abort: () → {Abort} Empty

def runState (init: s) (prog: () → {State s | e} a): {e} Pair a s :=
  let run: s → {e} Pair a s :=
    handle prog() with
      | return x => st => MkPair x st
      | get u, k => st => k st st
      | put st2, k => st => k() st2
  run init

def toOption (prog: () → {Abort | e} a): {e} Option a :=
  handle prog() with
    | return x => Some x
    | abort u, k => None

-- Reads two lines, counting them in the state, and prints the count.
def countIS(): {IO, State Nat} () :=
  let a := IO.readLine()
  put (get() + 1)
  let b := IO.readLine()
  put (get() + 1)
  IO.print (Nat.toText get())

-- The same, with the row the other way round.
def countSI(): {State Nat, IO} () :=
  let a := IO.readLine()
  put (get() + 1)
  let b := IO.readLine()
  put (get() + 1)
  IO.print (Nat.toText get())

-- `IO.simulate` outside, `runState` inside.
def stateInside (prog: () → {State Nat, IO} ()): Pair (List Text) Nat :=
  let r := IO.simulate ["x", "y"] (u => runState 10 prog)
  MkPair (printed r) (Pair.snd (result r))

-- `runState` outside, `IO.simulate` inside.
def stateOutside (prog: () → {State Nat, IO} ()): Pair (List Text) Nat :=
  let r := runState 10 (u => IO.simulate ["x", "y"] prog)
  MkPair (printed (Pair.fst r)) (Pair.snd r)

def checkCount (r: Pair (List Text) Nat): Bool := if eqTexts (Pair.fst r) ["12"] then Pair.snd r == 12 else False

test "IO then State, State handled inside" := checkCount (stateInside countIS)
test "IO then State, State handled outside" := checkCount (stateOutside countIS)
test "State then IO, State handled inside" := checkCount (stateInside countSI)
test "State then IO, State handled outside" := checkCount (stateOutside countSI)

-- Prints, then stops.
def printThenAbort(): {IO, Abort} Nat :=
  IO.print "before"
  let e := abort()
  IO.print "after"
  fromEmpty e

def abortThenPrint(): {Abort, IO} Nat :=
  IO.print "before"
  let e := abort()
  IO.print "after"
  fromEmpty e

-- With `toOption` inside, what was printed before the abort is kept.
test "abort inside simulate keeps earlier prints" :=
  let r := IO.simulate [] (u => toOption printThenAbort)
  if eqTexts (printed r) ["before"] then isNone (result r) else False

test "abort inside simulate, the other row order" :=
  let r := IO.simulate [] (u => toOption abortThenPrint)
  if eqTexts (printed r) ["before"] then isNone (result r) else False

-- With `toOption` outside, the abort discards the whole simulated run.
test "abort outside simulate discards the run" :=
  isNone (toOption (u => IO.simulate [] printThenAbort))

test "abort outside simulate, the other row order" :=
  isNone (toOption (u => IO.simulate [] abortThenPrint))

-- A program with no `IO` at all

test "a pure program prints nothing" :=
  let r := IO.simulate ["unused"] (u => 6 * 7)
  if eqTexts (printed r) [] then result r == 42 else False

test "a program with only State" :=
  let r := runState 1 (u => IO.simulate [] (v => put (get() + 1)))
  if eqTexts (printed (Pair.fst r)) [] then Pair.snd r == 2 else False

-- A long run

def printMany: Nat → {IO} ()
  | 0 => ()
  | Succ n =>
    IO.print "x"
    printMany n

test "5,000 prints" := List.length (printed (IO.simulate [] (u => printMany 5000))) == 5000

-- By computation

theorem greetOutput: printed (IO.simulate ["Ada"] greet) = ["Name?", "Hello, Ada!"] := rfl

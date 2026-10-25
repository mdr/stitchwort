import Std (Empty, Fail, List, Nat, Text)

def countdown (n: Nat): {Fail, Partial} Nat :=
  if n == 3 then Empty.absurd (Fail.stop "three") else if n == 0 then 0 else countdown (n - 1)

def spin (n: Nat): {Partial} Nat := spin n

def toResult (prog: () → {Fail, Partial | e} a): {Partial | e} Result a Text :=
  handle prog() with
    | return x => Ok x
    | Fail.stop msg, k => Err msg

def showResult: Result Nat Text → Text
  | Ok n => "Ok " ++ Nat.toText n
  | Err msg => "Err " ++ msg

def stopThenSpin (): {Fail, Partial} Nat :=
  let none := Fail.stop "no"
  spin 0

ability Input where
  next: () → {Input} (Option Text)

def fromLines (lines: List Text) (prog: () → {Input, Partial | e} a): {Partial | e} a :=
  let run: List Text → {Partial | e} a :=
    handle prog() with
      | return x => _ => x
      | next (), resume => rest =>
        match rest with
          | [] => resume None []
          | Cons line more => resume (Some line) more
  run lines

def play (turn: Nat): {Input, IO, Partial} Nat :=
  match next () with
    | None => turn
    | Some command =>
      IO.print ("turn " ++ Nat.toText turn ++ ": " ++ command)
      play (turn + 1)

ability Choice where
  fork: () → {Choice} Bool

def collectIn (prog: () → {Choice, Partial | e} a): {Partial | e} List a :=
  handle prog() with
    | return x => [x]
    | fork (), k => List.append (k True) (k False)

def search (n: Nat): {Choice, IO, Partial} Nat :=
  if n == 0 then 0 else
    let b := fork ()
    IO.print (Nat.toText n ++ (if b then "T" else "F"))
    let r := search (n - 1)
    2 * r + (if b then 1 else 0)

def showList: List Nat → Text
  | [] => ""
  | Cons x [] => Nat.toText x
  | Cons x rest => Nat.toText x ++ "," ++ showList rest

def leftLoops (): {Choice, IO, Partial} Nat :=
  let b := fork ()
  IO.print (if b then "left" else "right")
  if b then spin 0 else 1

ability Counter where
  get: () → {Counter} Nat
  incr: () → {Counter} ()

def runCounter (start: Nat) (prog: () → {Counter, Partial | e} a): {Partial | e} (a, Nat) :=
  let run: Nat → {Partial | e} (a, Nat) :=
    handle prog() with
      | return x => s => (x, s)
      | get (), k => s => k s s
      | incr (), k => s => k () (s + 1)
  run start

def tally (n: Nat): {Counter, IO, Partial} Nat :=
  if n == 0 then get () else
    incr ()
    let r := tally (n - 1)
    IO.print ("tally " ++ Nat.toText n ++ ": " ++ Nat.toText r)
    r + n

def walk (n: Nat): {IO, Partial} Nat :=
  if n == 0 then 0 else
    let (x, _) := runCounter 0 (() => tally n + walk (n - 1))
    IO.print ("walk " ++ Nat.toText n ++ ": " ++ Nat.toText x)
    x

def climb (n: Nat): {Counter, Fail, IO, Partial} Nat :=
  incr ()
  let c := get ()
  IO.print ("climb " ++ Nat.toText c)
  if c == 3 then Empty.absurd (Fail.stop "three") else climb (n + 1)

def countDown (n: Nat): {IO, Partial} Nat :=
  IO.print ("cd " ++ Nat.toText n)
  if n == 0 then 0 else n + countDown (n - 1)

ability Ask where
  ask: Nat → {Ask} Nat

def asking (): {Ask, IO} Nat :=
  let a := ask 2
  IO.print ("got " ++ Nat.toText a)
  a + ask 1

def answered (): {IO, Partial} Nat :=
  handle asking () with
    | return x => 100 * x + countDown 1
    | ask n, k => k (countDown n)

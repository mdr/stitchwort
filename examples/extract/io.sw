-- Pure exports that use `IO` inside, handled by the prelude's `IO.simulate`.
-- The scripted input lines are built from numbers: this example was
-- written before exports could take `Text`.
--
-- run: linesEchoed [] 5
-- run: linesEchoed [1, 2, 3] 5
-- run: linesEchoed [1, 2, 3] 2
-- run: numberedLength []
-- run: numberedLength [7, 42, 100]
-- run: countdownLines 4
-- run: oneEntryPerPrint 3

-- Echoes each line until the input runs out, reading at most `n` lines.
def echoLine: Option Text -> (() -> {IO} ()) -> {IO} ()
  | None, more => ()
  | Some l,  more =>
    IO.print l
    more()

def echo: Nat -> {IO} ()
  | 0      => ()
  | Succ n => echoLine (IO.readLine()) (u => echo n)

def linesOf: List Nat -> List Text
  | Nil       => Nil
  | Cons n ns => Cons (Nat.toText n) (linesOf ns)

-- How many lines `echo` printed, given those numbers as input lines.
export def linesEchoed (ns: List Nat) (bound: Nat): Nat := List.length (Pair.fst (IO.simulate (linesOf ns) (u => echo bound)))

-- Numbers each line ("1: 7", "2: 42", …).
def numberLine (i: Nat): Option Text -> (() -> {IO} ()) -> {IO} ()
  | None, more => ()
  | Some l,  more =>
    IO.print (Nat.toText i ++ ": " ++ l)
    more()

def numberFrom (i: Nat): Nat -> {IO} ()
  | 0      => ()
  | Succ n => numberLine i (IO.readLine()) (u => numberFrom (i + 1) n)

def totalLength: List Text -> Nat
  | Nil       => 0
  | Cons t ts => Text.length t + totalLength ts

-- The number of characters printed when numbering the lines.
export def numberedLength (ns: List Nat): Nat :=
  totalLength (Pair.fst (IO.simulate (linesOf ns) (u => numberFrom 1 (List.length ns))))

def countdown: Nat -> {IO} ()
  | 0      => IO.print "liftoff"
  | Succ n =>
    IO.print (Nat.toText (Succ n))
    countdown n

-- How many lines a countdown from `n` prints: `n + 1`.
export def countdownLines (n: Nat): Nat := List.length (Pair.fst (IO.simulate [] (u => countdown n)))

def printLines: Nat -> {IO} ()
  | 0      => ()
  | Succ n =>
    IO.print "a\nb"
    printLines n

-- A payload containing a line feed is still one entry.
export def oneEntryPerPrint (n: Nat): Bool := List.length (Pair.fst (IO.simulate [] (u => printLines n))) == n

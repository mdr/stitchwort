-- Pure exports that use `IO` inside, handled by the prelude's `simulate`.
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
echoLine : Maybe Text -> (() -> {IO} ()) -> {IO} ()
echoLine Nothing  more = ()
echoLine (Just l) more =
  print l
  more ()

echo : Nat -> {IO} ()
echo 0        = ()
echo (Succ n) = echoLine (readLine ()) (\u -> echo n)

linesOf : List Nat -> List Text
linesOf Nil         = Nil
linesOf (Cons n ns) = Cons (natToText n) (linesOf ns)

-- How many lines `echo` printed, given those numbers as input lines.
export
linesEchoed : List Nat -> Nat -> Nat
linesEchoed ns bound = length (fst (simulate (linesOf ns) (\u -> echo bound)))

-- Numbers each line ("1: 7", "2: 42", …).
numberLine : Nat -> Maybe Text -> (() -> {IO} ()) -> {IO} ()
numberLine i Nothing  more = ()
numberLine i (Just l) more =
  print (natToText i ++ ": " ++ l)
  more ()

numberFrom : Nat -> Nat -> {IO} ()
numberFrom i 0        = ()
numberFrom i (Succ n) = numberLine i (readLine ()) (\u -> numberFrom (i + 1) n)

totalLength : List Text -> Nat
totalLength Nil         = 0
totalLength (Cons t ts) = textLength t + totalLength ts

-- The number of characters printed when numbering the lines.
export
numberedLength : List Nat -> Nat
numberedLength ns =
  totalLength (fst (simulate (linesOf ns) (\u -> numberFrom 1 (length ns))))

countdown : Nat -> {IO} ()
countdown 0        = print "liftoff"
countdown (Succ n) =
  print (natToText (Succ n))
  countdown n

-- How many lines a countdown from `n` prints: `n + 1`.
export
countdownLines : Nat -> Nat
countdownLines n = length (fst (simulate [] (\u -> countdown n)))

printLines : Nat -> {IO} ()
printLines 0        = ()
printLines (Succ n) =
  print "a\nb"
  printLines n

-- A payload containing a line feed is still one entry.
export
oneEntryPerPrint : Nat -> Bool
oneEntryPerPrint n = length (fst (simulate [] (\u -> printLines n))) == n

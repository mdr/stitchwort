-- core/IO.sw. The `IO` ability and `IO.simulate`, which interprets it as
-- data. Loaded with the core: The runner calls `Std.Pair.fst (Std.IO.simulate
-- ...)`, and `IO` is a registry built-in (docs/proposals/prelude-slim.md
-- §2.1).

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- What `IO.console` reports: whether standard input and output are
-- terminals, and the terminal's size, 0 by 0 when it isn't known
-- (docs/proposals/terminal-io.md §4.2). A registry built-in, so the runners
-- can build it.
type Console = {
  inputIsTerminal: Bool,
  outputIsTerminal: Bool,
  columns: Nat,
  rows: Nat
}

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `IO.simulate` interprets them as data. `console`, `keysMode`,
-- `readBytes` and `write` are what a terminal handler is built on (docs/proposals/terminal-io.md §4). The host's
-- `print`, `readLine` and `readAll` leave keys mode first, if it's on.
ability IO where
  print: Text → {IO} () -- writes the text, then a line ending
  readLine: () → {IO} (Option Text) -- None only at end of input
  readAll: () → {IO} Text -- the rest of the input, all at once
  console: () → {IO} Console -- whether input and output are terminals, and the size
  keysMode: Bool → {IO} () -- enter (True) or leave (False) keys mode
  readBytes: () → {IO} (Option (List Nat)) -- the bytes of one read; None at end of input
  write: Text → {IO} () -- the text with no line ending, then flush
  randomSeed: () → {IO} Nat -- a fresh 64-bit number each run, from the host's entropy; 0 in `IO.simulate`

-- The first line of scripted input, if there is one.
def IO.nextLine: List Text → Option Text
  | Nil => None
  | Cons line lines => Some line

-- All of the scripted input, as `IO.readAll` gives it: each line followed by a
-- line feed, as a real interpreter would read it.
def IO.restOf (ins: List Text): Text :=
  MkText (List.concatMap ins (line => List.append (Text.toList line) ['\n']))

-- The UTF-8 encoding of a character: one to four bytes.
def Char.utf8 (c: Char): List Nat :=
  let n := Char.toNat c
  if Nat.leq n 127 then [n]
  else if Nat.leq n 2047 then [192 + n / 64, 128 + n % 64]
  else if Nat.leq n 65535 then [224 + n / 4096, 128 + n / 64 % 64, 128 + n % 64]
  else [240 + n / 262144, 128 + n / 4096 % 64, 128 + n / 64 % 64, 128 + n % 64]

-- All of the scripted input as `IO.readBytes` gives it, in one read: the
-- UTF-8 of `IO.restOf`, or `None` once no lines remain.
def IO.bytesOf: List Text → Option (List Nat)
  | Nil => None
  | ins => Some (List.concatMap (Text.toList (IO.restOf ins)) Char.utf8)

-- `IO.console` under `IO.simulate`: no terminals, and the size isn't known.
def IO.noConsole: Console := { inputIsTerminal = False, outputIsTerminal = False, columns = 0, rows = 0 }

-- Runs a program against scripted input lines: each `IO.readLine` takes the
-- next one, and gives `None` once they're used up; `IO.readAll` takes all
-- that are left (see `IO.restOf`), after which `IO.readLine` gives `None`
-- and `IO.readAll` gives "". `IO.readBytes` also takes all that are left, as
-- UTF-8 in one read (`IO.bytesOf`), and gives `None` once nothing is. Records
-- each `IO.print` and `IO.write` payload, in order, with the result. A
-- payload is one entry even if it contains a line feed: a real interpreter
-- writes each `print` payload followed by a line ending. `IO.console` says
-- there's no terminal (`IO.noConsole`), `IO.keysMode` does nothing, and
-- `IO.randomSeed` gives 0. The payloads are collected in reverse and turned
-- round at the end, so a long run doesn't build a deep chain of pending
-- pairs.
def IO.simulate (input: List Text) (prog: () → {IO | e} a): {e} Pair (List Text) a :=
  let run: List Text → List Text → {e} Pair (List Text) a :=
    handle prog() with
      | return x => ins out => MkPair (List.reverseOnto out Nil) x
      | IO.print t, k => ins out => k() ins (Cons t out)
      | IO.readLine u, k => ins out => k (IO.nextLine ins) (List.tailOf ins) out
      | IO.readAll u, k => ins out => k (IO.restOf ins) Nil out
      | IO.console u, k => ins out => k IO.noConsole ins out
      | IO.keysMode on, k => ins out => k() ins out
      | IO.readBytes u, k => ins out => k (IO.bytesOf ins) Nil out
      | IO.write t, k => ins out => k() ins (Cons t out)
      | IO.randomSeed u, k => ins out => k 0 ins out
  run input Nil

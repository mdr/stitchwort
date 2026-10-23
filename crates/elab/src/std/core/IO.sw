-- core/IO.sw. The `IO` ability and `IO.simulate`, which interprets it as
-- data. Loaded with the core: The runner calls `Std.Pair.fst (Std.IO.simulate
-- ...)`, and `IO` is a registry built-in (docs/proposals/prelude-slim.md
-- §2.1).

-- Input and output (docs/proposals/text-and-io.md, Part 2)

-- The console. Only a host interpreter performs these for real; in Stitchwort
-- code, `IO.simulate` interprets them as data.
ability IO where
  print: Text -> {IO} () -- writes the text, then a line ending
  readLine: () -> {IO} (Option Text) -- None only at end of input
  readAll: () -> {IO} Text -- the rest of the input, all at once

-- The first line of scripted input, if there is one.
def IO.nextLine: List Text -> Option Text
  | Nil => None
  | Cons line lines => Some line

-- All of the scripted input, as `IO.readAll` gives it: each line followed by a
-- line feed, as a real interpreter would read it.
def IO.restOf (ins: List Text): Text :=
  MkText (List.concatMap (line => List.append (Text.toList line) ['\n']) ins)

-- Runs a program against scripted input lines: each `IO.readLine` takes the
-- next one, and gives `None` once they're used up; `IO.readAll` takes all
-- that are left (see `IO.restOf`), after which `IO.readLine` gives `None`
-- and `IO.readAll` gives "". Records each `IO.print` payload, in order, with the
-- result. A payload is one entry even if it contains a line feed: a real
-- interpreter writes each payload followed by a line ending. The payloads
-- are collected in reverse and turned round at the end, so a long run
-- doesn't build a deep chain of pending pairs.
def IO.simulate (input: List Text) (prog: () -> {IO | e} a): {e} Pair (List Text) a :=
  let run: List Text -> List Text -> {e} Pair (List Text) a :=
    handle prog() with
      | return x => ins out => MkPair (List.reverseOnto out Nil) x
      | IO.print t, k => ins out => k() ins (Cons t out)
      | IO.readLine u, k => ins out => k (IO.nextLine ins) (List.tailOf ins) out
      | IO.readAll u, k => ins out => k (IO.restOf ins) Nil out
  run input Nil

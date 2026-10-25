-- STAND-IN, to be deleted at the switch-over (docs/proposals/terminal-io.md
-- §8, lanes 1 and 2). `HostIO` has exactly the four host operations lane 1
-- adds to `IO` (`console`, `keysMode`, `readBytes`, `write`, and the
-- `Console` record), so `Terminal.toHost` can be written against them before
-- they exist. `HostIO.toIO` performs them with today's `IO`, as the host
-- will when neither input nor output is a terminal: no terminal, 0 by 0,
-- keys mode does nothing, and the whole input is one read.
--
-- Switching over (`Terminal.toIO` in Terminal.sw marks the spot): delete
-- this file and its line in `crates/elab/src/library.rs`; in Terminal.sw,
-- write `IO.` for `HostIO.` and `Console` for `HostIO.Console`, drop
-- `HostIO` from the rows, and make `Terminal.toIO` the body of
-- `Terminal.toHost`; write `Char.utf8` for `Key.utf8` and delete
-- `Key.utf8`; and turn `HostIO.scripted` into a test-only handler of `IO`
-- for the tests that need a terminal.

-- Whether input and output are terminals, and the size (0 by 0 when it
-- isn't known). Lane 1's `Console`.
type HostIO.Console = { inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }

ability HostIO where
  console: () → {HostIO} HostIO.Console -- whether input and output are terminals, and the size
  keysMode: Bool → {HostIO} () -- enter (True) or leave (False) keys mode
  readBytes: () → {HostIO} (Option (List Nat)) -- the bytes of one read; None at end of input
  write: Text → {HostIO} () -- the text with no line ending, then flush

-- Not a terminal on either side.
def HostIO.noTerminal: HostIO.Console := { inputIsTerminal = False, outputIsTerminal = False, columns = 0, rows = 0 }

-- The host operations with today's `IO`, as on pipes: the rest of the input
-- is one read, as UTF-8 (each line ending in a line feed, as `IO.readAll`
-- gives it), then `None`. `write` can't leave out the line ending, but it
-- isn't used: output isn't a terminal.
def HostIO.toIO (prog: () → {HostIO, IO | e} a): {IO | e} a :=
  handle prog() with
    | return result => result
    | console (), resume => resume HostIO.noTerminal
    | keysMode on, resume => resume ()
    | readBytes (), resume =>
      let text := IO.readAll ()
      resume (if Text.isEmpty text then None else Some (List.concatMap (Text.toList text) Key.utf8))
    | write text, resume =>
      IO.print text
      resume ()

-- For tests: a host whose console is `console`, whose reads are `reads`, in
-- order (then `None`), and which records every `write`, and every time keys
-- mode goes on or off (as "keys on" and "keys off"), in order. Like the
-- real host, `keysMode` does nothing when the mode is already as asked.
def HostIO.scripted (console: HostIO.Console) (reads: List (List Nat)) (prog: () → {HostIO | e} a): {e} Pair (List Text) a :=
  let run: List (List Nat) → Bool → List Text → {e} Pair (List Text) a :=
    handle prog() with
      | return result => readsLeft keysOn written => MkPair (List.reverse written) result
      | console (), resume => readsLeft keysOn written => resume console readsLeft keysOn written
      | keysMode on, resume => readsLeft keysOn written =>
        if on == keysOn then resume () readsLeft keysOn written
        else resume () readsLeft on (Cons (if on then "keys on" else "keys off") written)
      | readBytes (), resume => readsLeft keysOn written =>
        match readsLeft with
          | [] => resume None [] keysOn written
          | [bytes, ..later] => resume (Some bytes) later keysOn written
      | write text, resume => readsLeft keysOn written => resume () readsLeft keysOn (Cons text written)
  run reads False []

-- `Terminal`: read single keys and draw whole screens
-- (docs/proposals/terminal-io.md). A program reads keys with
-- `Terminal.readKey` and draws frames with `Terminal.draw`; it never sees
-- escape bytes, raw mode or the cursor. `Terminal.toIO` runs it on the
-- console, and `Terminal.simulate` runs it in tests, from scripted keys.
--
--   def play (state: Game): {Terminal, Partial} Game :=
--     Terminal.draw (view state)
--     match Terminal.readKey () with
--       | None => state
--       | Some (Printable 'q') => state
--       | Some key => play (update state key)
--
--   def main (): {IO, Partial} () :=
--     let final := Terminal.toIO (() => play newGame)
--     IO.print "You quit with ${final.gold} gold."
--
-- Key decoding is `Key.next` (Key.sw), colours are `Ansi` (Ansi.sw).

import Key.Decoded (Got, Incomplete, NoBytes)

-- A terminal's size, in characters.
type Terminal.Size = { columns: Nat, rows: Nat }

-- The three operations (D1247): keys in, whole frames out.
ability Terminal where
  readKey: () → {Terminal} (Option Key) -- the next key; None only at end of input
  draw: List Text → {Terminal} () -- replaces the whole screen with these lines
  size: () → {Terminal} Terminal.Size -- the screen's size (80 by 24 when it isn't known)

-- Frames

-- A frame as one text for a terminal: cursor home, the lines, each followed
-- by "clear to end of line" and separated by CR LF, then "clear to end of
-- screen". No full clear, so the screen doesn't flicker; no CR LF after the
-- last line, so a frame as tall as the screen doesn't scroll it.
def Frame.ansi (lines: List Text): Text := "\u{1b}[H${Frame.ansiLines lines}\u{1b}[J"

def Frame.ansiLines: List Text → Text
  | [] => ""
  | [line] => "${line}\u{1b}[K"
  | [line, ..more] => "${line}\u{1b}[K\r\n${Frame.ansiLines more}"

-- A frame as lines, when output isn't a terminal: the lines, then a line
-- holding just a form feed to mark the end of the frame.
def Frame.plain (lines: List Text): List Text := List.append lines ["\u{c}"]

-- Reading keys

-- What `Terminal.nextKey` gives: the key (None at end of input), the bytes
-- read but not decoded yet, and where reading goes on from.
type Terminal.Read (source: Type) = { key: Option Key, pending: List Nat, source: source }

-- How many more reads may complete a key cut off by the end of a read: as
-- many as the longest sequence `Key.next` waits for, so reading is bounded.
def Terminal.moreReads: Nat := 16

-- The next key: decoded from `pending`, the bytes left from earlier reads,
-- or from a new read when there are none. `read` reads once from `source`.
-- A key cut off at the end of the bytes is finished by reading more
-- (at most `moreReads` times), except an escape sequence cut off on a
-- terminal: a terminal writes a sequence in one go, so the end of its read
-- ends the sequence (terminal-io.md §3.2). A cut-off lone `ESC` is
-- `Escape`, and any other cut-off key `Unknown`.
--
-- Generic in how bytes are read, so tests can give the reads as a list
-- (`Terminal.keysOfReads`), and `Terminal.toIO` reads from the host.
def Terminal.nextKey (inputIsTerminal: Bool) (read: s → {e} Pair (Option (List Nat)) s) (pending: List Nat) (source: s): {e} Terminal.Read s :=
  match pending with
    | [] => Terminal.afterRead inputIsTerminal read Terminal.moreReads [] (read source)
    | _ => Terminal.decode inputIsTerminal read Terminal.moreReads pending source

-- Decodes `bytes`, which aren't empty, reading up to `reads` more times to
-- finish a cut-off key.
def Terminal.decode (inputIsTerminal: Bool) (read: s → {e} Pair (Option (List Nat)) s): Nat → List Nat → s → {e} Terminal.Read s
  | reads, bytes, source =>
    match Key.next bytes with
      | Got key rest => { key = Some key, pending = rest, source = source }
      | NoBytes => { key = None, pending = [], source = source }
      | Incomplete =>
        match reads with
          | 0 => Terminal.cutOff bytes source
          | Succ more =>
            if Terminal.readsOn inputIsTerminal bytes then Terminal.afterRead inputIsTerminal read more bytes (read source)
            else Terminal.cutOff bytes source

-- After a read, with `bytes` before it: end of input (or an empty read)
-- ends them; otherwise decode the two together.
def Terminal.afterRead (inputIsTerminal: Bool) (read: s → {e} Pair (Option (List Nat)) s) (reads: Nat) (bytes: List Nat):
    Pair (Option (List Nat)) s → {e} Terminal.Read s
  | MkPair None source => Terminal.ended bytes source
  | MkPair (Some []) source => Terminal.ended bytes source
  | MkPair (Some more) source => Terminal.decode inputIsTerminal read reads (List.append bytes more) source

-- Whether to read more to finish the cut-off key at the front of `bytes`:
-- from a pipe always, and from a terminal unless it's an escape sequence.
def Terminal.readsOn (inputIsTerminal: Bool): List Nat → Bool
  | [27, .._] => !inputIsTerminal
  | _ => True

-- The input ended with `bytes` undecoded: none at all is the end, and any
-- others are a cut-off key.
def Terminal.ended (bytes: List Nat) (source: s): Terminal.Read s :=
  match bytes with
    | [] => { key = None, pending = [], source = source }
    | _ => Terminal.cutOff bytes source

-- A key cut off: `Escape` for a lone `ESC`, `Unknown` for anything else.
def Terminal.cutOff (bytes: List Nat) (source: s): Terminal.Read s :=
  { key = Some (if bytes == [27] then Escape else Unknown), pending = [], source = source }

-- Every key that `reads`, one list of bytes per read, decode to: what
-- `readKey` gives, call after call, on input that arrives so. For tests.
def Terminal.keysOfReads (inputIsTerminal: Bool) (reads: List (List Nat)): List Key :=
  Terminal.keysWithin inputIsTerminal (List.length (List.concat reads) + List.length reads + 1) [] reads

-- At most `limit` keys (every key but the last uses up a byte or a read).
def Terminal.keysWithin (inputIsTerminal: Bool): Nat → List Nat → List (List Nat) → List Key
  | 0, pending, reads => []
  | Succ limit, pending, reads =>
    let next := Terminal.nextKey inputIsTerminal Terminal.readFromList pending reads
    match next.key with
      | None => []
      | Some key => Cons key (Terminal.keysWithin inputIsTerminal limit next.pending next.source)

-- One read from a list of reads: its first, then the rest.
def Terminal.readFromList: List (List Nat) → Pair (Option (List Nat)) (List (List Nat))
  | [] => MkPair None []
  | [bytes, ..later] => MkPair (Some bytes) later

-- The handlers

-- The size `console` gives, with 80 columns or 24 rows where it doesn't
-- know (0).
def Terminal.sizeOf (console: Console): Terminal.Size :=
  { columns = if console.columns == 0 then 80 else console.columns, rows = if console.rows == 0 then 24 else console.rows }

-- Draws a frame: on a terminal as one text, `Frame.ansi` of the lines that
-- fit on the screen (lines wider than it are cut off by the terminal, since
-- keys mode turns wrapping off); otherwise as plain lines, `Frame.plain`.
def Terminal.drawFrame (console: Console) (lines: List Text): {IO} () :=
  if console.outputIsTerminal then IO.write (Frame.ansi (List.take lines (Terminal.sizeOf console).rows))
  else Terminal.printLines (Frame.plain lines)

def Terminal.printLines: List Text → {IO} ()
  | [] => ()
  | [line, ..more] =>
    IO.print line
    Terminal.printLines more

-- `Terminal` on the console: keys from standard input, frames to standard
-- output, through the host's `IO.console`, `IO.keysMode`, `IO.readBytes`
-- and `IO.write`. Keys mode goes on at the first `readKey` or `draw` (a
-- program that only asks the size never changes the terminal), and off when
-- the program returns. Each `readKey` reads at most `1 + Terminal.moreReads`
-- times, so this handler is total: around a total program it's total, and
-- around a partial one partial (D1259). The program's own `IO.print` and
-- `IO.readLine` pass through to the host, which leaves keys mode for them
-- (D1260).
def Terminal.toIO (prog: () → {Terminal, IO | e} a): {IO | e} a :=
  let inputIsTerminal := (IO.console ()).inputIsTerminal
  let run: List Nat → {IO | e} a :=
    handle prog() with
      | return result => pending =>
        IO.keysMode False
        result
      | readKey (), resume => pending =>
        IO.keysMode True
        let next := Terminal.nextKey inputIsTerminal (u => MkPair (IO.readBytes ()) u) pending ()
        resume next.key next.pending
      | draw lines, resume => pending =>
        IO.keysMode True
        Terminal.drawFrame (IO.console ()) lines
        resume () pending
      | size (), resume => pending => resume (Terminal.sizeOf (IO.console ())) pending
  run []

-- For tests: `readKey` gives the scripted keys in order, then `None`. Every
-- frame drawn is recorded, in order, with the result. The size is 80 by 24.
-- No `IO` is involved, so a game's tests need no input text.
def Terminal.simulate (keys: List Key) (prog: () → {Terminal | e} a): {e} Pair (List (List Text)) a :=
  let run: List Key → List (List Text) → {e} Pair (List (List Text)) a :=
    handle prog() with
      | return result => keysLeft frames => MkPair (List.reverse frames) result
      | readKey (), resume => keysLeft frames =>
        match keysLeft with
          | [] => resume None [] frames
          | [key, ..later] => resume (Some key) later frames
      | draw lines, resume => keysLeft frames => resume () keysLeft (Cons lines frames)
      | size (), resume => keysLeft frames => resume { columns = 80, rows = 24 } keysLeft frames
  run keys []

-- Tests

test "Frame: ansi" := Frame.ansi ["ab", "c"] == "\u{1b}[Hab\u{1b}[K\r\nc\u{1b}[K\u{1b}[J"
test "Frame: ansi of no lines" := Frame.ansi [] == "\u{1b}[H\u{1b}[J"
test "Frame: plain" := Frame.plain ["ab", "c"] == ["ab", "c", "\u{c}"]

-- Reading keys, as `readKey` does, from reads given as lists.
test "reads: the native prototype's reads, from a terminal" :=
  Terminal.keysOfReads True [[97], [27, 91, 65], [27], [1], [13], [113]] == [Printable 'a', Up, Escape, Ctrl 'a', Enter, Printable 'q']
test "reads: piped, one chunk" := Terminal.keysOfReads False [[107, 27, 91, 66, 113]] == [Printable 'k', Down, Printable 'q']
test "reads: piped, a sequence split across reads" := Terminal.keysOfReads False [[107, 27], [91], [66, 113]] == [Printable 'k', Down, Printable 'q']
test "reads: a terminal, the same reads: the end of a read ends a sequence" :=
  Terminal.keysOfReads True [[107, 27], [91], [66, 113]] == [Printable 'k', Escape, Printable '[', Printable 'B', Printable 'q']
test "reads: a terminal, a CSI cut off by a read is Unknown" :=
  Terminal.keysOfReads True [[27, 91, 49], [120]] == [Unknown, Printable 'x']
test "reads: a lone ESC at the end of input is Escape" := Terminal.keysOfReads False [[120, 27]] == [Printable 'x', Escape]
test "reads: a cut-off sequence at the end of input is Unknown" := Terminal.keysOfReads False [[27, 91, 49]] == [Unknown]
test "reads: a UTF-8 character split across reads, piped" := Terminal.keysOfReads False [[226], [130], [172, 33]] == [Printable '€', Printable '!']
test "reads: a UTF-8 character split across reads, from a terminal" := Terminal.keysOfReads True [[226, 130], [172]] == [Printable '€']
test "reads: a cut-off UTF-8 character at the end of input is Unknown" := Terminal.keysOfReads False [[97, 226, 130]] == [Printable 'a', Unknown]
test "reads: unknown sequences and bad bytes" :=
  Terminal.keysOfReads True [[27, 91, 49, 59, 53, 65], [255], [120]] == [Unknown, Unknown, Printable 'x']
test "reads: an empty read is the end of input" := Terminal.keysOfReads False [[97], [], [98]] == [Printable 'a']
test "reads: none" := Terminal.keysOfReads True [] == []
-- `ESC [` then parameter bytes, one per read: after 16 more reads the key is
-- cut off, and the reads after that are keys of their own.
test "reads: a sequence that never ends stops after the reads allowed" :=
  Terminal.keysOfReads False (Cons [27, 91] (List.replicate 20 [48])) == Cons Unknown (List.replicate 4 (Printable '0'))

-- `simulate`.

-- Draws a frame per key until `q` or the keys run out (at most 10), and
-- gives the keys it read.
def Terminal.echoKeys: Nat → List Key → {Terminal} (List Key)
  | 0, seen => List.reverse seen
  | Succ limit, seen =>
    Terminal.draw ["${List.length seen} keys"]
    match Terminal.readKey () with
      | None => List.reverse seen
      | Some (Printable 'q') => List.reverse seen
      | Some key => Terminal.echoKeys limit (Cons key seen)

test "simulate: a frame per draw, and the keys in order" :=
  Terminal.simulate [Up, Printable 'x', Printable 'q', Down] (() => Terminal.echoKeys 10 []) ==
    MkPair [["0 keys"], ["1 keys"], ["2 keys"]] [Up, Printable 'x']
test "simulate: None after the keys" :=
  Terminal.simulate [Enter] (() => Terminal.echoKeys 10 []) == MkPair [["0 keys"], ["1 keys"]] [Enter]
test "simulate: the size" :=
  let size := Pair.snd (Terminal.simulate [] (() => Terminal.size ()))
  size.columns == 80 && size.rows == 24

-- `toIO` under `IO.simulate`: the input is decoded as keys, and the frames
-- come out as printed lines with a form feed after each.
test "toIO: under IO.simulate" :=
  IO.simulate ["ab", "q"] (() => Terminal.toIO (() => Terminal.echoKeys 10 [])) ==
    MkPair ["0 keys", "\u{c}", "1 keys", "\u{c}", "2 keys", "\u{c}", "3 keys", "\u{c}"] [Printable 'a', Printable 'b', Enter]
test "toIO: the program's own prints pass through" :=
  let run := IO.simulate [] (() => Terminal.toIO (() =>
    IO.print "before"
    Terminal.draw ["frame"]
    IO.print "after"))
  Pair.fst run == ["before", "frame", "\u{c}", "after"]
test "toIO: the size, unknown on a pipe" :=
  let size := Pair.snd (IO.simulate [] (() => Terminal.toIO (() => Terminal.size ())))
  size.columns == 80 && size.rows == 24

-- `toIO` on a scripted terminal.

-- For tests: `IO` as a host whose console is `console` and whose reads are
-- `reads`, in order (then `None`). Records every `write` and `print`, and
-- every time keys mode goes on or off (as "keys on" and "keys off"), in
-- order. Like the real host, `keysMode` does nothing when the mode is
-- already as asked, and `print` leaves keys mode first (D1260). There are no
-- lines to read: `readLine` gives `None`, `readAll` "", `randomSeed` 0.
def Terminal.scriptedHost (console: Console) (reads: List (List Nat)) (prog: () → {IO | e} a): {e} Pair (List Text) a :=
  let run: List (List Nat) → Bool → List Text → {e} Pair (List Text) a :=
    handle prog() with
      | return result => readsLeft keysOn written => MkPair (List.reverse written) result
      | IO.print text, resume => readsLeft keysOn written =>
        resume () readsLeft False (Cons text (if keysOn then Cons "keys off" written else written))
      | IO.readLine u, resume => readsLeft keysOn written => resume None readsLeft keysOn written
      | IO.readAll u, resume => readsLeft keysOn written => resume "" readsLeft keysOn written
      | IO.console u, resume => readsLeft keysOn written => resume console readsLeft keysOn written
      | IO.keysMode on, resume => readsLeft keysOn written =>
        if on == keysOn then resume () readsLeft keysOn written
        else resume () readsLeft on (Cons (if on then "keys on" else "keys off") written)
      | IO.readBytes u, resume => readsLeft keysOn written =>
        match readsLeft with
          | [] => resume None [] keysOn written
          | [bytes, ..later] => resume (Some bytes) later keysOn written
      | IO.write text, resume => readsLeft keysOn written => resume () readsLeft keysOn (Cons text written)
      | IO.randomSeed u, resume => readsLeft keysOn written => resume 0 readsLeft keysOn written
  run reads False []

def Terminal.testTerminal: Console := { inputIsTerminal = True, outputIsTerminal = True, columns = 20, rows = 2 }

test "toIO: on a terminal, keys mode on at the first draw and off at the end; frames as ANSI text cut to the screen" :=
  Terminal.scriptedHost Terminal.testTerminal [[106], [27], [113]] (() => Terminal.toIO (() => Terminal.echoKeys 10 [])) ==
    MkPair ["keys on", Frame.ansi ["0 keys"], Frame.ansi ["1 keys"], Frame.ansi ["2 keys"], "keys off"] [Printable 'j', Escape]
test "toIO: a tall frame is cut to the screen's rows" :=
  let run := Terminal.scriptedHost Terminal.testTerminal [] (() => Terminal.toIO (() => Terminal.draw ["1", "2", "3"]))
  Pair.fst run == ["keys on", Frame.ansi ["1", "2"], "keys off"]
test "toIO: asking only the size leaves the terminal alone" :=
  let run := Terminal.scriptedHost Terminal.testTerminal [] (() => Terminal.toIO (() => Terminal.size ()))
  let size := Pair.snd run
  Pair.fst run == [] && size.columns == 20 && size.rows == 2
test "toIO: a print between frames leaves keys mode, and the next draw enters it again" :=
  let run := Terminal.scriptedHost Terminal.testTerminal [] (() => Terminal.toIO (() =>
    Terminal.draw ["a"]
    IO.print "note"
    Terminal.draw ["b"]))
  Pair.fst run == ["keys on", Frame.ansi ["a"], "keys off", "note", "keys on", Frame.ansi ["b"], "keys off"]

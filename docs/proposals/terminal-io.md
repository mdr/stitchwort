# Stitchwort: terminal control

**Status:** draft 2, 25 October 2026, for review (D1245). Nothing here is built. Draft 1's D1246 to D1248 are decided: D1246 as revised below (a library ability), D1247 and D1248 as recommended. Draft 1's random-seed decision is renumbered **D1258** (it clashed with D1249, the partial-handlers note) and is still open. New decisions D1259 and D1260 are at the end.

Matt asked for "simple keypress input, or maybe more generally a bit of terminal control layer stuff as needed in IO, to make this nice". A roguelike is being written now. It needs to react to single keys (including arrow keys) and redraw the screen without scrolling.

**What changed from draft 1.** `Terminal` is now a library ability written in Stitchwort, in std, like `Fail` and `Each`. A std handler, `Terminal.toIO`, interprets it into four new basic `IO` operations, and `Terminal.simulate`, also in std, runs it in tests. Key decoding (bytes to `Key`) and frame drawing (lines to ANSI text) are ordinary Stitchwort functions, testable and provable; draft 1's Rust and JavaScript decoders and frame writers are gone. Handlers can wrap partial code (D1254 to D1256, [partial-handlers.md](partial-handlers.md), being built), so a game loop is `Partial` with no fuel, and `toIO` and `simulate` need no special signature. `main`'s row doesn't change: a program handles `Terminal` itself.

Tags: **[source]** read in the code, **[ran]** run in a scratch prototype, **[web]** checked online (linked), **[inferred]** reasoned but not run, **[speculative]** a guess.

## 1. The proposal in brief

```
-- std/Terminal/Terminal.sw (sketch)

type Key: Type =
  | Printable (char: Char) -- a printable character, space included (not `Char`: see §3.7)
  | Enter
  | Tab
  | Backspace
  | Escape
  | Delete
  | Up
  | Down
  | Left
  | Right
  | Home
  | End
  | PageUp
  | PageDown
  | Ctrl (letter: Char) -- Ctrl with a letter: `Ctrl 'a'`, and so on
  | Unknown -- bytes that aren't one of the above (D1259)

ability Terminal where
  readKey: () → {Terminal} (Option Key) -- the next key; None only at end of input
  draw: List Text → {Terminal} () -- replaces the whole screen with these lines
  size: () → {Terminal} { columns: Nat, rows: Nat }

-- For real: each operation as a few basic `IO` operations (§3.4).
def Terminal.toIO (prog: () → {Terminal, IO | e} a): {IO | e} a

-- For tests: `readKey` takes the next scripted key, then gives None. Records
-- every frame drawn, in order. The size is 80 by 24.
def Terminal.simulate (keys: List Key) (prog: () → {Terminal | e} a): {e} (List (List Text), a)
```

And in `std/core/IO.sw`, four new host operations (§4):

```
ability IO where
  print: Text → {IO} () -- as today
  readLine: () → {IO} (Option Text) -- as today
  readAll: () → {IO} Text -- as today
  console: () → {IO} Console -- whether input and output are terminals, and the size
  keysMode: Bool → {IO} () -- enter (True) or leave (False) keys mode
  readBytes: () → {IO} (Option (List Nat)) -- the bytes of one read; None at end of input
  write: Text → {IO} () -- the text with no line ending, then flush
```

- **Three `Terminal` operations.** A program reads keys and draws whole frames (D1247). It never sees escape bytes, raw mode, cursor movement or screen clearing: `toIO` does those.
- **Colour is plain text.** Pure std helpers (`Ansi.colour Red "@"`, `Ansi.bold`, `Ansi.reverse`, `Ansi.strip`) wrap text in ANSI colour codes. A frame's lines may contain them. Nothing else in the frame is interpreted.
- **`main` is unchanged:** `{IO}`, `{Fail, IO}`, and their partial forms. A program handles `Terminal` with `toIO` inside `main`, so the runners never meet a third ability.
- **The runner still owns the parts a handler can't do** (§5): putting the terminal back after a crash, a signal or a panic, and catching the signals.
- **Random seed:** still proposed as one more host operation, `IO.randomSeed` (D1258, §7).

A game's outline, with handlers around partial code (D1254, D1255):

```
-- One turn per key, until the player quits or the keys run out.
def play (state: Game): {Terminal, Partial} Game :=
  Terminal.draw (view state)
  match Terminal.readKey () with
    | None => state
    | Some (Printable 'q') => state
    | Some key => play (update state key)

def main (): {IO, Partial} () :=
  let final := Terminal.toIO (() => play (newGame (IO.randomSeed ())))
  IO.print "You quit with ${final.gold} gold."

test "q quits at once, after one frame" :=
  let (frames, final) := Terminal.simulate [Printable 'q'] (() => play (newGame 0))
  frames.length == 1
```

`play` is `Partial`, as any unbounded interactive loop is ([text-and-io.md](text-and-io.md), "What the guarantee says"), and there's no fuel. `toIO` returns when `play` does, leaving keys mode first, so the final `IO.print` appears on the normal screen, below the shell prompt where the game started. The test is a partial test (D1183); it ends because the scripted keys end.

## 2. Which operations, and where

| Need | Where it goes | Why |
|---|---|---|
| One key without Enter, arrows as a `Key` | `Terminal.readKey`; decoding in Stitchwort (§3.2); the bytes from `IO.readBytes` | Only the host can switch off line editing and echo; turning bytes into keys needs nothing from the host |
| Clear the screen, move the cursor | Inside `draw`, in Stitchwort (§3.3) | A frame replaces the screen, so programs never position the cursor |
| Write without a line ending | `IO.write`, used by `toIO` only | A frame is written as one text; programs use `draw` |
| Raw mode, alternate screen, hidden cursor, no wrap | `IO.keysMode` (§4.2) | Terminal settings need a system call; and the runner must be able to undo exactly what was done (§5) |
| Terminal size, whether there is a terminal | `IO.console` | Only the host knows |
| Colours, bold, reverse video | Pure std helpers producing ANSI text | They're just text; tests can `Ansi.strip` them |
| Restore on exit, panic, `Fail`, Ctrl-C | The runner (§5) | A handler's `return` clause doesn't run when the program fails or is interrupted |
| Unread input kept across mode switches | The runner (§4.4) | It's how the host reads, not something a program sees |

**Why whole frames (D1247, decided).** This is the shape the popular libraries settled on: Bubble Tea's `View()` returns the whole screen after every update ([tea.go](https://github.com/charmbracelet/bubbletea/blob/main/tea.go)), brick's `appDraw :: s -> [Widget n]` draws the state ([Brick/Main.hs](https://github.com/jtdaugherty/brick/blob/master/src/Brick/Main.hs)), vty's `update :: Picture -> IO ()` outputs a picture ([Graphics.Vty](https://hackage.haskell.org/package/vty/docs/Graphics-Vty.html)), and notty's `Term.image t i` "sets `i` as `t`'s current image and redraws the terminal" ([Notty_unix.Term](https://pqwy.github.io/notty/doc/notty/Notty_unix/Term/index.html)). Tests compare screens as lists of lines; it works unchanged without a terminal; and programs have no cursor state to get wrong. The cost: a program can't update one cell cheaply. Redrawing an 80×24 screen is about 2 KB per key press, which a terminal handles easily. (Speculative: no measurement; vty and Bubble Tea diff frames for this reason, and `toIO` could too, later, without changing the ability. Finer control can come later if needed.)

**Left out:** mouse, resize events, function keys, Alt combinations, modified arrows (Ctrl-Up and so on, which arrive as `Unknown`), bracketed paste, key releases and timed reads (`readKey` with a timeout, for real-time games). A turn-based roguelike needs none of them. A program that cares about resizing calls `size()` before each frame.

## 3. The library side (std)

### 3.1 Why a library ability (D1246, decided)

- **Decoding and drawing become ordinary code.** Escape sequences, UTF-8 and frame text are pure functions over lists, unit-tested in Stitchwort and open to theorems (§3.6), and written once rather than in Rust and in JavaScript.
- **`main` and the runners don't change shape.** `MainRow` (`crates/rt/src/ir.rs`, two cases, `Io` and `FailIo`) **[source]**, the driver's candidate annotations and the JS `perform` stay as they are. Draft 1 needed all three to learn a third ability. The runners learn four `IO` operations instead, which is the kind of change `readAll` was.
- **The type still says what code needs.** `play`'s type has `Terminal`; `main`'s has only `IO`. A program that doesn't call `toIO` never changes the terminal's mode, as before, but that now shows in the code rather than in `main`'s type.
- **`IO.simulate` keeps its type.** It gains a clause for each new operation (§4.5), and `Terminal.simulate` is the test handler for terminal programs.

### 3.2 Decoding keys

`Key.next (bytes: List Nat): Decoded` decodes the first key in a list of bytes. `Decoded` is `Got key rest`, `Incomplete` (the bytes end inside a sequence) or `Empty`. It's total and structural, with no `IO`:

- **Control bytes:** CR or LF is `Enter` (so piped CR LF is two `Enter`s, which a game ignores); 9 is `Tab`; 127 or 8 is `Backspace`; other bytes 1 to 26 are `Ctrl` with a letter (`Ctrl 'a'` for 1). Bytes 0 and 28 to 31 are `Unknown`.
- **Printable ASCII and UTF-8:** a character of one to four bytes is `Printable`. A bad lead or continuation byte, or a code that isn't a scalar value (`Char.fromNat` gives `None`), is `Unknown`. Draft 1 made invalid UTF-8 `E-IO`, as for `readLine`; a key decoder has no reason to stop the program for a stray byte.
- **Escape sequences:** `ESC [` followed by parameter bytes and a final byte is a CSI sequence: `ESC [A` to `ESC [D` are the arrows, `ESC [H` and `ESC [F` `Home` and `End`, `ESC [3~` `Delete`, `ESC [5~` and `ESC [6~` `PageUp` and `PageDown` (and `ESC [1~`, `[4~`, `[7~`, `[8~` for `Home` and `End`). `ESC O` followed by one byte is the SS3 form some terminals send for arrows, `Home` and `End`. Any other complete sequence (`ESC [1;5A`, Ctrl-Up) is one `Unknown`.
- **`ESC` followed by anything else** is `Escape`, then that byte decodes on its own.

**Telling a lone `ESC` from the start of a sequence.** `Key.next` says `Incomplete` for an `ESC` at the end of the bytes; the handler decides, from where the bytes came from:

- **On a terminal, a read ends where the terminal stopped writing.** A terminal writes an escape sequence in one go, so it arrives in one read (both prototypes saw `[27,91,65]` in one read, §4.6). So a sequence cut off by the end of a read is finished: a lone `ESC` is `Escape`, and anything else cut off is `Unknown`. This is the "one read" rule of draft 1. It needs the host to say where a read ended, which is why `IO.readBytes` returns one read's bytes as a list, rather than a stream of bytes.
- **From a pipe or file, read boundaries mean nothing**, so a sequence cut off by a read is completed by reading more: at most 16 more reads, the longest sequence the decoder accepts, so the handler stays total. At end of input, a lone `ESC` is `Escape` and anything else cut off is `Unknown`.
- **A UTF-8 character cut off by a read** is completed the same way in both cases (speculative whether a terminal ever splits one; reading more is right either way).

(Speculative in general: over a slow link a terminal's sequence could be split. The native runner could make `readBytes` wait briefly with `poll` after a lone `ESC`, later, with no change to the library; the native prototype shows `poll` works.)

### 3.3 Drawing frames

`Frame.ansi (lines: List Text): Text` is the frame as one text: cursor home (`ESC [H`), the lines, each followed by "clear to end of line" (`ESC [K`) and separated by CR LF, then "clear to end of screen" (`ESC [J`). There's no full clear, so the screen doesn't flicker. Two fixes over draft 1:

- **No CR LF after the last line**, so a frame as tall as the screen doesn't scroll it by one line **[inferred]**.
- **`toIO` drops lines below the screen's last row** before writing, for the same reason. Lines wider than the screen are cut off by the terminal, since keys mode turns off wrapping.

**When output isn't a terminal, `draw` writes plain lines:** each line with `IO.print`, then a line holding just a form feed (U+000C) to mark the end of a frame, as in draft 1. `Frame.plain (lines: List Text): List Text` gives those lines.

### 3.4 `Terminal.toIO`

```
def Terminal.toIO (prog: () → {Terminal, IO | e} a): {IO | e} a :=
  let console := IO.console ()
  let run: List Nat → {IO | e} a :=
    handle prog() with
      | return result => _ =>
        IO.keysMode False
        result
      | readKey (), resume => pending =>
        IO.keysMode True
        let (key, rest) := Terminal.nextKey console.inputIsTerminal pending
        resume key rest
      | draw lines, resume => pending =>
        IO.keysMode True
        Terminal.drawFrame (IO.console ()) lines
        resume () pending
      | size (), resume => pending => resume (Terminal.sizeOf (IO.console ())) pending
  run []
```

- **The state is the pending bytes**: what was read but not yet decoded, as the roguelike's `fromLines` keeps pending commands **[source]** (`games/rogue/src/Rogue/Input.sw`).
- **`nextKey`** decodes from the pending bytes, and calls `IO.readBytes` once when they're empty, plus at most 16 more to finish a sequence from a pipe (§3.2). Its loop is bounded, so `toIO`'s clauses are total, and `toIO` adds no `Partial` of its own: wrapped round a total program it's total, and round a partial one it's partial (D1255).
- **Entering keys mode lazily**, at the first `readKey` or `draw`, means a program that only asks the `size` never touches the terminal. `IO.keysMode True` when already in keys mode does nothing.
- **Size:** `IO.console` gives 0 by 0 when the size isn't known (a fresh pseudo-terminal does, §4.6); `sizeOf` makes that 80 by 24.

**Why `Unknown` is a key (D1259).** Skipping unknown sequences inside `toIO`, as draft 1 did in Rust, means a loop that reads until a key it knows comes along. That loop waits on the user, so it's unbounded, and it would make `toIO` always partial: `{IO, Partial | e}`, even round a total program. Returning `Unknown` keeps every `readKey` to one read (or a bounded few from a pipe), and the skipping happens in the program's own loop, which is already `Partial`. Bubble Tea 1.x's input reader makes a similar choice: a byte it can't decode becomes an event, `unknownInputByteMsg`, rather than being dropped, because "having this event makes it possible to troubleshoot invalid inputs" ([key.go at v1.3.4](https://github.com/charmbracelet/bubbletea/blob/v1.3.4/key.go)) **[web]**. A game's `match` has a catch-all case anyway (`| Some key => play (update state key)`, with `update` ignoring keys it doesn't use).

**`IO.print` inside `toIO`.** A handler handles one ability (`E-ABILITY`, "a handler handles one ability", `crates/elab/src/effects.rs` line 3738) **[source]**, so `toIO` handles only `Terminal`, and the program's own `IO.print`, `IO.readLine` and `IO.readAll` pass through it to the host. So the host's `print`, `readLine` and `readAll` leave keys mode first, if it's on; the next `readKey` or `draw` enters it again. That keeps draft 1's mixing rule: a debugging `IO.print` in the middle of a game, or a "name your character" `IO.readLine`, behaves as it does in a plain program. (The alternative, a second handler in `toIO` that handles `IO` and passes it on, is possible but forwards all seven operations and needs `toIO` to track the mode itself; the one-line host rule is simpler.)

### 3.5 `Terminal.simulate`

Handles `Terminal` alone: scripted keys in (then `None`), frames recorded in order, size 80 by 24. It doesn't involve `IO`, so a test of a game needs no input text at all. To test `toIO` itself, decoding and plain frames included, a test runs `IO.simulate input (() => Terminal.toIO prog)` (§4.5): the scripted input is decoded as keys, and the frames come out as print payloads with form-feed lines between them.

### 3.6 Tests and a theorem

- **Unit tests** of `Key.next` for every key, the `ESC O` forms, UTF-8 of each length, a character and a sequence split across reads (from a pipe and from a terminal), lone `ESC`, `Unknown` sequences and bad bytes; `Frame.ansi` and `Frame.plain`; `simulate` recording one frame per `draw` and `None` after the keys; `toIO` under `IO.simulate`.
- **A theorem**, as the round trip a terminal makes: `Key.bytes: Key → List Nat` gives the bytes a terminal sends for each non-character key, and `Key.next (Key.bytes key ++ rest) = Got key rest` for every such key but `Escape`, and every `rest`. (`Escape` needs `rest` not to start with `[` or `O`: that's the lone-`ESC` ambiguity of §3.2, stated as a theorem.) It's a case split with one `rfl` per key: the prototype proves the `Up`, `Delete` and `Enter` cases by `rfl` for a free `rest` **[ran]**, and the others have the same shape **[inferred]**. The same for `Printable` (UTF-8 encoding of every scalar value decodes back) is harder, needing arithmetic on the four length ranges; it's a stretch goal for the lane, not a requirement.

### 3.7 The prototype **[ran]**

A scratch project (not committed; about 270 lines) wrote `Key`, `Key.next`, `Frame.ansi`, `Terminal`, `Terminal.simulate`, and a handler like `toIO`, interpreting `Terminal` into a stand-in `Host` ability with `readBytes`, `write` and a plain-lines output (the real `IO` operations don't exist yet), with a scripted `Host` handler taking a list of reads. It ran on today's `main` (release build), with a fuelled loop reading keys, since partial handlers aren't built yet:

```
Proto
  ✓ letters, arrows, lone ESC, Ctrl, Enter        ran
  ✓ piped: one chunk                              ran
  ✓ piped: a sequence split across chunks         ran
  ✓ terminal: ESC at the end of a read is Escape  ran
  ✓ SS3 arrows                                    ran
  ✓ tilde keys                                    ran
  ✓ UTF-8 and a split character from a pipe       ran
  ✓ unknown sequences are Unknown                 ran
  ✓ frame text                                    ran
  ✓ simulate records frames                       ran
10 test(s): 10 passed, 0 failed (0 from the cache)
```

- The first test feeds the reads the native prototype saw (`[97]`, `[27,91,65]`, `[27]`, `[1]`, `[13]`, `[113]`, §4.6) and gets `Printable 'a'`, `Up`, `Escape`, `Ctrl 'a'`, `Enter`, `Printable 'q'`: the same keys as draft 1's Rust decoder.
- "A sequence split across chunks" is `[107, 27]`, `[91]`, `[66, 113]` from a pipe: `k`, `Down`, `q`. The same bytes as a terminal's reads give `k`, `Escape`, `[`, `B`, by the one-read rule.
- "Unknown sequences" is `ESC [1;5A` (Ctrl-Up), byte 255, then `x`: `Unknown`, `Unknown`, `Printable 'x'`.
- The handler type-checks as `{Host | e} a` with no `Partial`: the bounded read loop of §3.4 passes the totality checker as written **[ran]**.
- **A naming finding:** the constructor can't be called `Char`, as in draft 1: `E-MUTUAL-CONSTRUCTOR`, "`Char` can't be used in the constructors of `Key`, which declares it", because the field `(char: Char)` then means the constructor. Draft 2 calls it `Printable`.

The prototype lived in session scratch space and isn't kept; lane 2 writes the real thing.

## 4. The host layer

### 4.1 What the runners do with input today

- **Native** (`crates/cli/src/main.rs`, `run_main`): standard input is `std::io::stdin().lock()`, a buffered reader, and output a `BufWriter`. `crates/rt/src/host.rs` reads lines with `read_until(b'\n')`; the output is flushed before every read (`crates/rt/src/run.rs`, `perform`).
- **Reference evaluator** (`crates/driver/src/run.rs`): the same `BufRead` and `host.rs` functions.
- **`run --js`** (`crates/js/src/run.rs`): `main` runs in a worker thread, which reads file descriptor 0 itself with `fs.readSync`, in 64 KB chunks, waiting with `Atomics.wait` when it isn't ready. It doesn't use `process.stdin`.
- **Playground** (`crates/web/src/lib.rs`): the input box's whole text is the input, as `Scripted`, a `BufRead` whose `fill_buf` returns all the text that's left **[source]**, passed to the same `run_main_fast` as the native runner.

### 4.2 The four new operations

| Operation | Native and reference (Unix) | `run --js` | Playground | `IO.simulate` |
|---|---|---|---|---|
| `console ()` | `isatty` on descriptors 0 and 1; size by `TIOCGWINSZ` on output, 0 by 0 if it fails | `tty.isatty(0)` and `(1)`; size from the main thread (§4.7) | Not terminals; 0 by 0 | Not terminals; 0 by 0 |
| `keysMode True` | If input is a terminal: raw mode (§4.3). If output is a terminal: alternate screen, hidden cursor, no wrap. Remembered, so it can be undone. Nothing if already on | The same, through `stty` (§4.7) | Nothing | Nothing |
| `keysMode False` | Undoes exactly what `True` did. Nothing if off | The same | Nothing | Nothing |
| `readBytes ()` | Flush output; then `fill_buf` on the shared reader: what's buffered, or one blocking read; `None` at end of input | One `readSync` into the existing buffer, waiting with `Atomics.wait` | The input box's remaining text as UTF-8, in one read; then `None` | The rest of the scripted input as UTF-8, each line ending in LF (as `readAll` gives it), in one read; then `None` |
| `write t` | The text's UTF-8, no line ending, then flush | The same | Appended to the output | One payload |

- **`Console`** is a record type in `std/core/IO.sw`: `{ inputIsTerminal: Bool, outputIsTerminal: Bool, columns: Nat, rows: Nat }`. Like `Option` for `readLine`, it's a registry built-in, so the runners can build it. One operation rather than four, since `toIO` wants them together.
- **Bytes are `List Nat`**, each below 256 by the host's promise. A `Byte` type isn't needed for this; a read is a few bytes per key. (`List (Fin 256)` would put the bound in the type, at the cost of proofs in every decoder step; not worth it here **[inferred]**.)
- **`readBytes` and `readLine` share one reader**, so bytes buffered by one are seen by the other, in order.
- **`print`, `readLine` and `readAll` leave keys mode first**, if it's on (§3.4). This is the one piece of mode logic in the host besides `keysMode` itself.
- **What keys mode means when only one side is a terminal.** Input a terminal, output piped (`stitchwort run game.sw > log`): raw mode on input, no escape codes on output, and `toIO` draws plain lines because `console` says output isn't a terminal. Input piped, output a terminal (`printf 'jjq' | stitchwort run game.sw`): no terminal settings change, the screen setup is written, and `toIO` draws with `Frame.ansi`. Both piped: nothing changes, and the game plays from the bytes, as `printf 'jjk\033[Aq' | stitchwort run game.sw | less`.

### 4.3 Keys mode on a terminal

`keysMode True`, if standard input is a terminal, saves the terminal settings and:

- turns off line editing and echo (`ICANON`, `ECHO`, `IEXTEN`), and `IXON` (so Ctrl-S and Ctrl-Q are keys) and `ICRNL` (so Enter is CR);
- **keeps `ISIG`, so Ctrl-C and Ctrl-\ still stop the program** (D1248, decided), but disables the suspend character, so Ctrl-Z is `Ctrl 'z'`. (Suspending a program in keys mode would leave the shell's terminal in keys mode; speculative how each shell copes, so it's simply avoided.)

and, if standard output is a terminal, writes: alternate screen (`ESC [?1049h`), hidden cursor (`ESC [?25l`) and line wrapping off (`ESC [?7l`), so a line wider than the screen is cut off rather than wrapped. `keysMode False` writes the reverse (`ESC [?7h`, `ESC [?25h`, `ESC [?1049l`) and restores the saved settings.

These are in the host, not written by `toIO` with `IO.write`, so that the runner always knows exactly what to undo after a crash (§5).

### 4.4 What stays in the runner

- **Restoring the terminal however the program ends** (§5): a handler's `return` clause runs only when the program returns.
- **The signal setup**, before any thread starts (§5).
- **Unread input across mode switches.** In keys mode the terminal hands over each key as soon as it's pressed, so a read returns one key's bytes, and a buffered reader just passes them on (the prototype reads keys through `stdin().lock()` and gets one read per key, §4.6). Anything left in the buffer when the mode changes belongs to the next read, so mode switches use `TCSANOW`, not `TCSAFLUSH`, which discards unread input. With a `print` between frames leaving keys mode, that matters: typed-ahead keys survive.

### 4.5 How the playground and `IO.simulate` see them

- **The playground** gets the pipe form for nothing: `console` says no terminal, the input box's text is decoded as keys, and the frames appear in the output as lines, with a form-feed line after each. Keys pressed live in the page would need the machine to pause at `readBytes` and resume when a key comes, which `run_main_fast` can't do today; that's later work with its own trigger. Arrow keys can't be typed into the box, so letter keys (`hjkl`) are the playground's way to move. The playground's host is the same generic `BufRead` code as the native runner's (§4.1), so `readBytes` there is one `fill_buf`: the whole remaining text.
- **`IO.simulate`** keeps its type, `{e} (List Text, a)`, and gains four clauses: `console` gives no terminals and 0 by 0; `keysMode` does nothing; `readBytes` gives the rest of the scripted input, UTF-8 encoded, in one read, then `None` (afterwards `readLine` gives `None` and `readAll` gives "", as after `readAll` today); `write t` records `t` as one payload. Since `console` says output isn't a terminal, `toIO` under `IO.simulate` never calls `write`: frames arrive as `print` payloads. The UTF-8 encoder `IO.simulate` needs (`Char.utf8: Char → List Nat`) goes in `std/core`, next to `IO.simulate`, and is also what the decoder's round-trip theorem is about.

### 4.6 Native: confirmed by a prototype (draft 1)

A scratch program (not committed) did keys mode with `nix::sys::termios`, ran in a pseudo-terminal driven by a Python script, and recorded the terminal flags from outside:

```
read 1 bytes -> [Char('a')]
read 3 bytes -> [Up]
read 1 bytes -> [Escape]
read 1 bytes -> [Ctrl('a')]
read 1 bytes -> [Enter]
read 1 bytes -> [Char('q')]
while running: {'ICANON': False, 'ECHO': False, 'ISIG': True}
after exit:    {'ICANON': True, 'ECHO': True, 'ISIG': True}
```

Sending Ctrl-C (byte 3) instead: `signal SIGINT: terminal restored`, exit status 130, and the flags restored as above. Piped input (`printf 'k\033[Bq' | rawproto`) gave `[Char('k'), Down, Char('q')]` with no terminal calls. `rustix::termios::tcgetwinsize` returned 0 by 0 in the Python pseudo-terminal, which is why the 80 by 24 fallback exists. (That prototype decoded in Rust; draft 2 decodes the same byte sequences in Stitchwort, §3.7.)

**Dependencies: nothing new.** `nix` 0.31.3, with its `term`, `signal` and `poll` features, is already a normal dependency of `stitchwort-cli` through `rustyline` (`cargo tree -i nix -e features`), and its `tcgetattr`, `tcsetattr` and `SigSet::wait` are safe functions, so no `unsafe` is needed. For the size, `rustix` 1.1.5 is already in `Cargo.lock` (through `tempfile`); its `termios` feature gives a safe `tcgetwinsize`. No new crate means nothing new to fetch in the Nix build. `crossterm` wasn't tried: it isn't in the tree, and these two cover everything.

**Where the code lives.** `crates/rt` is also built for WebAssembly, so it can't call `termios`. The runner's `perform` gets the terminal side of `console` and `keysMode` through a small trait in `crates/rt/src/host.rs`, with a "no terminal" implementation there (used by the reference evaluator when not on a terminal, the playground and the tests) and the terminal one in `crates/cli`, under `cfg(unix)`. `readBytes` and `write` need no trait: they're generic over `BufRead` and `Write`, like `read_line`.

### 4.7 Node (`run --js`): confirmed by a prototype (draft 1)

Node's own raw mode, `setRawMode`, doesn't fit:

- it belongs to `process.stdin` in the main thread, but the program runs in a worker, where "`process.stdin` … may be redirected by the parent thread" ([worker_threads](https://nodejs.org/api/worker_threads.html));
- in raw mode "Ctrl+C will no longer cause a `SIGINT`" ([tty](https://nodejs.org/api/tty.html#readstreamsetrawmodemode)), which goes against D1248.

Instead, `keysMode True` in the worker runs `stty -icanon -echo -iexten -ixon -icrnl min 1 time 0 susp undef` through `execSync` with standard input inherited (`stty` changes the terminal on its standard input), and the worker keeps reading descriptor 0 as today. The launcher saves `stty -g` first and restores it on the worker's exit and on `SIGINT`, `SIGTERM` and `SIGHUP`. A scratch launcher and worker in a pseudo-terminal showed:

- keys arrived one read each, as natively (`[97]`, `[27,91,65]`, `[27]`, `[1]`, `[13]`, `[113]`), and the flags were restored after exit;
- **`process.exit(130)` in the main thread hung** while the worker was blocked in `readSync`, for over 20 seconds until killed. Restoring the terminal, removing the handler and sending `SIGINT` to itself again works: the process ended at once, killed by `SIGINT`, with the terminal restored;
- the Nix shell's GNU `stty` restoring `stty -g` output on macOS printed "unable to perform all requested operations" and exited with 1, but the flags were restored. The runner ignores `stty`'s exit status when restoring.

**The size** comes from the main thread, which owns `process.stdout`: a `tty.WriteStream`'s `columns` and `rows` are "updated whenever the `'resize'` event is emitted" ([tty](https://nodejs.org/api/tty.html#writestreamcolumns)) **[web]**. The launcher writes them into the shared memory the worker already waits on, on start and on each `'resize'`, so `console` is a read, not a process spawned per frame (`stty size` would be). Whether a worker's own `process.stdout.columns` works isn't checked **[speculative]**; this route doesn't need it.

### 4.8 Windows

Out of scope. Nothing in the project targets Windows today. The terminal side is `cfg(unix)`; elsewhere `console` says there's no terminal, and programs get the pipe form.

## 5. Safety: putting the terminal back

The runner knows whether keys mode is on, because `keysMode` is its own operation. It undoes it however the program ends:

| How the program ends | Native | `run --js` |
|---|---|---|
| Returns normally | `toIO`'s `return` clause has already left keys mode; the guard checks anyway | The worker's exit handler restores |
| `Fail` unhandled, `E-IO`, `E-RESOURCE` | `toIO`'s `return` clause doesn't run. These are `Err` results of `run_main`, so a guard value restores as the function returns | The worker exits, the main thread restores |
| A Rust panic (an internal bug) | The guard's `Drop` restores (the workspace uses the default `panic = "unwind"`) | Not applicable |
| Ctrl-C, Ctrl-\, `kill`, closed terminal | The runner blocks `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` before starting any thread, and a waiting thread restores (if keys mode is on) and exits with 130 (`SigSet::wait`, as in the prototype) | The main thread's handlers restore, then re-raise the signal |
| `kill -9`, a crash of the runner itself | Can't be caught. The user types `reset` | Same |

Ctrl-C works even while the program is busy computing and not reading keys, because `ISIG` stays on. That's the main reason for D1248: a `Partial` game loop with a bug that never reads a key can still be stopped.

**Piped input** never changes terminal settings; with output a terminal, the screen setup is still undone as above.

## 6. Randomness and time (D1258, was D1249)

A roguelike needs a different dungeon each run; today's roguelike starts every game from the same seed, `defaultSeed = 2026` (`games/rogue/src/Rogue/Rogue.sw`) **[source]**. **Recommendation: one host operation, `IO.randomSeed: () → {IO} Nat`**, a fresh 64-bit number each run (from the operating system's random source natively, `crypto.getRandomValues` in Node and the browser). Everything else is pure: a small `Random` module in std (a seed in, a number and the next seed out), so dungeon generation is testable and replayable from a seed. `IO.simulate` gives the seed 0. A test that wants another seed calls the pure code with it.

- **Why not a seed argument?** `main` takes `()`, and `stitchwort run` passes no arguments today. Adding command-line arguments is a bigger change with its own design.
- **Why not the clock?** A turn-based game doesn't need it, and a clock as a seed is worse than a random seed. Time becomes worth adding with timed reads, for real-time games; neither has a trigger yet.
- **Why in `IO`, not its own ability?** It's general, not about terminals, and it's one host operation, like the four in §4.

Prior art agrees on the shape: Lean seeds its `IO.rand` generator from 8 random bytes at start-up ([Random.lean](https://github.com/leanprover/lean4/blob/master/src/Init/Data/Random.lean): `IO.getRandomBytes 8`), and Unison's runtime provides `IO.randomBytes` and `IO.systemTime` as builtins ([Builtin.hs](https://github.com/unisonweb/unison/blob/trunk/parser-typechecker/src/Unison/Builtin.hs)).

## 7. Prior art

| Language or library | Key input | Screen output | Restoring the terminal |
|---|---|---|---|
| **Koka** | Only `readline()`, a line at a time ([std/os/readline.kk](https://github.com/koka-lang/koka/blob/master/lib/std/os/readline.kk)); nothing for single keys in `std/os` | `print` and `println` in the `console` effect ([std/core/console.kk](https://github.com/koka-lang/koka/blob/master/lib/std/core/console.kk)) | Not applicable |
| **Unison** | Builtins on handles: `IO.getChar`, `IO.setEcho`, `IO.setBuffering`, `IO.ready` ([Builtin.hs](https://github.com/unisonweb/unison/blob/trunk/parser-typechecker/src/Unison/Builtin.hs)) | Text to a handle | Up to the program |
| **OCaml `Unix`** | `tcgetattr` and `tcsetattr` with `c_icanon`, `c_echo`, `c_isig` fields ([unix.mli](https://github.com/ocaml/ocaml/blob/trunk/otherlibs/unix/unix.mli)) | Text | Up to the program |
| **OCaml notty** | `Term.event` gives a key, `` `Resize ``, or `` `End `` ([Notty_unix.Term](https://pqwy.github.io/notty/doc/notty/Notty_unix/Term/index.html)) | `Term.image` redraws a whole image; alternate screen, cursor hidden | `Term.create ~dispose:true` restores at exit; `nosig` (on by default) turns off Ctrl-C |
| **Haskell vty** | `nextEvent :: IO Event`; `EvKey Key [Modifier]`, with `KChar`, `KUp`, `KEsc`, `KEnter`, … ([Events.hs](https://github.com/jtdaugherty/vty/blob/master/src/Graphics/Vty/Input/Events.hs)) | `update :: Picture -> IO ()` ([Graphics.Vty](https://hackage.haskell.org/package/vty/docs/Graphics-Vty.html)) | `shutdown` "is necessary to cleanly restore the terminal state" |
| **Haskell brick** | `appHandleEvent` gets each event | `appDraw :: s -> [Widget n]` ([Brick/Main.hs](https://github.com/jtdaugherty/brick/blob/master/src/Brick/Main.hs)) | The library, around the app |
| **Bubble Tea (Go, the Elm architecture)** | `Update(Msg)` gets key messages; in 1.x an undecodable byte becomes `unknownInputByteMsg` ([key.go at v1.3.4](https://github.com/charmbracelet/bubbletea/blob/v1.3.4/key.go)) | `View()` renders the whole UI after every update ([tea.go](https://github.com/charmbracelet/bubbletea/blob/main/tea.go)) | The library |
| **Lean 4** | `getLine` on a stream; no raw mode in core | `putStr`; streams can say `isTty` ([IO.lean](https://github.com/leanprover/lean4/blob/master/src/Init/System/IO.lean)) | Not applicable |

The low-level designs (Unison, OCaml `Unix`) give echo and buffering switches and leave restoring to the program. The libraries people use for games and TUIs (notty, vty, brick, Bubble Tea) all give the same three things: an event or key type, "draw this whole picture", and the library putting the terminal back. Draft 2 has the same split as those libraries: a few host primitives underneath (here, four `IO` operations), the key type and drawing in the library, and, because a Stitchwort program can't catch a signal or a panic, the runner as the last line for putting the terminal back. Its `Key` is a subset of vty's, plus `Unknown`.

## 8. Build plan

Each step is one lane, stage-sized, running only the tests it names.

1. **Host `IO` operations in the runners.** `console`, `keysMode`, `readBytes`, `write` in the registry, `std/core/IO.sw` (with `Console` and `Char.utf8`) and `IO.simulate`'s four clauses; `perform` in the native runner, the reference evaluator, the playground and the JS worker, with the "no terminal" behaviour of §4.2 everywhere; `print`, `readLine` and `readAll` leaving keys mode. Native keys mode in `crates/cli` under `cfg(unix)`: raw mode and screen setup, `TCSANOW`, the size, the guard and the signal thread (§4.3, §5). Tests: `IO.simulate` clauses; a tiny program using the four operations directly, run piped by `run`, `run --reference` and the playground, agreeing; `stitchwort run` in a pseudo-terminal (the `pty` feature of `nix`, a crate already in the tree, as a dev-dependency) checking the flags after normal exit, `Fail`, `E-IO` and Ctrl-C.
2. **std `Terminal`.** `Key`, `Key.next`, `Frame.ansi`, `Frame.plain`, `Terminal`, `Terminal.toIO`, `Terminal.simulate`, and an `Ansi` module (`colour`, `bold`, `reverse`, `strip`). The tests of §3.6, the `Key.bytes` round-trip theorem, and a small example, a walking `@` that `hjkl` and arrows move (fuelled until lane 5's prerequisite lands, or written after it). Needs lane 1's operations; can start in parallel against a stand-in, as the prototype did, and switch over at merge.
3. **Node raw mode.** The `run --js` launcher and worker, as in §4.7: `stty`, the restore paths, the re-raised signal, the size through shared memory. Tests: the pseudo-terminal cases of lane 1, against `run --js`. After lane 1.
4. **The random seed** (if D1258 is yes). `IO.randomSeed` in every runner, seed 0 in `IO.simulate`, and a pure generator in std with its tests. Independent of the others; it touches the same `IO` declaration as lane 1, a cheap merge.
5. **The roguelike switch-over**, after partial handlers (D1254, D1255) land and lanes 1 and 2 merge. `play` partial with no fuel, as [partial-handlers.md](partial-handlers.md) §7.1 sketches; `Input` answered from `Terminal.readKey` (arrows as well as `hjkl`) instead of lines; `draw` through `Terminal.draw`; `IO.randomSeed` if lane 4 is in. Its tests move to `Terminal.simulate` with keys, plus one through `IO.simulate` and `toIO` for the whole `main`.

Lanes 1 and 4 can start now; 2 alongside 1; 3 after 1; 5 last.

## Decisions

Decided: **D1246** (revised: `Terminal` a library ability in std, `toIO` and `simulate` in std, decoding and drawing in Stitchwort), **D1247** (whole frames), **D1248** (Ctrl-C and Ctrl-\ still stop the program).

**D1258 (was D1249). Add one host operation, `IO.randomSeed: () → {IO} Nat`, with randomness itself pure in std, and no clock for now?** **Decided (Matt): yes.**
Context: a roguelike needs a different game each run, and today's always starts from seed 2026; `main` takes no arguments, so a seed can't be passed in. `IO.simulate` would give 0. Lean seeds its generator the same way. Time waits for real-time games (§6).
Recommendation: **yes.**

**D1259. Should `readKey` give an `Unknown` key for byte sequences it doesn't recognise, instead of skipping them?** **Decided (Matt): yes.**
Context: skipping means `toIO` waits, in a loop, for a key it knows, and a loop that waits on the user makes `toIO` partial even round a total program. With `Unknown`, each `readKey` does one read (a bounded few from a pipe), `toIO` stays total, and programs ignore `Unknown` in the catch-all case they have anyway. Bubble Tea passes unknown sequences on in a similar way (§3.4).
Recommendation: **yes.**

**D1260. Should the host's `print`, `readLine` and `readAll` switch out of keys mode by themselves, if it's on?**
Context: `toIO` can only handle `Terminal` (a handler handles one ability), so a program's own `IO.print` or `IO.readLine` in the middle of a game reaches the host while the terminal is in keys mode, and would print without line breaks on the game's screen or read with no echo. With this rule they work as in a plain program, and the next `draw` or `readKey` goes back into keys mode, keeping typed-ahead keys. The alternative is to leave them as they are and say "don't do that" (§3.4).
Recommendation: **yes.**

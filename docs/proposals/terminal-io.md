# Stitchwort: terminal control

**Status:** draft 1, 25 October 2026, for review (D1245). Nothing here is built. Decisions D1246 to D1249 are at the end.

Matt asked for "simple keypress input, or maybe more generally a bit of terminal control layer stuff as needed in IO, to make this nice". A roguelike is being written now. It needs to react to single keys (including arrow keys) and redraw the screen without scrolling. This note proposes a small `Terminal` ability for that, how each runner performs it, how the terminal is always put back, and one host operation for a random seed.

## 1. The proposal in brief

```
-- std/Terminal/Terminal.sw (sketch)

type Key: Type =
  | Char (char: Char) -- a printable character, space included
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

ability Terminal where
  readKey: () → {Terminal} (Option Key) -- the next key; None only at end of input
  draw: List Text → {Terminal} () -- replaces the whole screen with these lines
  size: () → {Terminal} { columns: Nat, rows: Nat }

-- Runs a program against scripted keys: `readKey` takes the next one, then
-- gives None. Records every frame drawn, in order. The size is 80 by 24.
def Terminal.simulate (keys: List Key) (prog: () → {Terminal | e} a): {e} Pair (List (List Text)) a
```

- **Three operations.** A program reads keys and draws whole frames. It never sees escape bytes, raw mode, cursor movement or screen clearing: the runner does those.
- **Colour is plain text.** Pure std helpers (`Ansi.colour Red "@"`, `Ansi.bold`, `Ansi.reverse`, `Ansi.strip`) wrap text in ANSI colour codes. A frame's lines may contain them. Nothing else in the frame is interpreted.
- **`main` may use it:** `main: () → {IO, Terminal, Fail, Partial} ()` and every smaller row. A game loop that runs until the player quits is `Partial`, as any unbounded interactive loop already is ([text-and-io.md](text-and-io.md), "What the guarantee says").
- **The runner owns the terminal.** It switches into "keys mode" at the first `Terminal` operation and back at the next `IO` operation or at exit, however the program ends.
- **`IO` gains one operation:** `IO.randomSeed: () → {IO} Nat`, a fresh 64-bit number each run (D1249).

A game's outline:

```
def play (state: Game): {IO, Terminal, Partial} () :=
  Terminal.draw (view state)
  match Terminal.readKey () with
    | None => ()
    | Some (Char 'q') => IO.print "You quit with ${state.gold} gold."
    | Some key => play (update state key)

def main (): {IO, Terminal, Partial} () := play (newGame (IO.randomSeed ()))
```

The final `IO.print` appears on the normal screen, after the game's screen has gone (§3.2).

## 2. Which operations

| Need | Where it goes | Why |
|---|---|---|
| One key without Enter, arrows as a `Key` | `Terminal.readKey` | Only the host can switch off line editing and echo |
| Write without a line ending | Not needed: `draw` covers it | A frame is written whole, so no partial lines are needed for a TUI |
| Clear the screen, move the cursor | Inside `draw` (the runner) | A frame replaces the screen, so programs never position the cursor |
| Hide and show the cursor | The runner, in keys mode | Every game wants it hidden; nothing to decide per program |
| Terminal size | `Terminal.size` | Only the host knows it |
| Colours, bold, reverse video | Pure std helpers producing ANSI text | They're just text; tests can `Ansi.strip` them |
| Restore on exit, panic, `Fail`, Ctrl-C | The runner (§4) | A program can't be trusted to do it; it may fail or be interrupted |

**Why whole frames, not `write` plus cursor operations (D1247).** This is the shape the popular libraries settled on: Bubble Tea's `View()` returns the whole screen after every update ([tea.go](https://github.com/charmbracelet/bubbletea/blob/main/tea.go)), brick's `appDraw :: s -> [Widget n]` draws the state ([Brick/Main.hs](https://github.com/jtdaugherty/brick/blob/master/src/Brick/Main.hs)), vty's `update :: Picture -> IO ()` outputs a picture ([Graphics.Vty](https://hackage.haskell.org/package/vty/docs/Graphics-Vty.html)), and notty's `Term.image t i` "sets `i` as `t`'s current image and redraws the terminal" ([Notty_unix.Term](https://pqwy.github.io/notty/doc/notty/Notty_unix/Term/index.html)). For Stitchwort it has three extra benefits:

- **Tests are easy.** `Terminal.simulate` records frames as `List Text`, so a test says "after these keys, the screen is this", with no terminal model.
- **It works without a terminal.** When output isn't a terminal, and in the playground, a frame is just lines of text (§3.3).
- **Fewer operations.** No cursor, clear, or write-without-newline operations, and no state for programs to get wrong.

The cost: a program can't update one cell cheaply. Redrawing a 80×24 screen is about 2 KB per key press, which a terminal handles easily. (Speculative: no measurement; vty and Bubble Tea diff frames for this reason, and the runner could too, later, without changing the ability.)

**Left out:** mouse, resize events, function keys, Alt combinations, bracketed paste, key releases and timed reads (`readKey` with a timeout, for real-time games). A turn-based roguelike needs none of them. A program that cares about resizing calls `size()` before each frame.

## 3. How the runners do it

### 3.1 What they do with input today

- **Native** (`crates/cli/src/main.rs`, `run_main`): standard input is `std::io::stdin().lock()`, a buffered reader, and output a `BufWriter`. `crates/rt/src/host.rs` reads lines with `read_until(b'\n')`; the output is flushed before every read (`crates/rt/src/run.rs`, `perform`).
- **Reference evaluator** (`crates/driver/src/run.rs`): the same `BufRead` and `host.rs` functions.
- **`run --js`** (`crates/js/src/run.rs`): `main` runs in a worker thread, which reads file descriptor 0 itself with `fs.readSync`, in 64 KB chunks, waiting with `Atomics.wait` when it isn't ready. It doesn't use `process.stdin`.
- **Playground** (`crates/web/src/lib.rs`): the input box's whole text is the input (`Scripted`), passed to the same `run_main_fast` as the native runner.

**Does buffering conflict with keys mode? No, as long as everything reads through the same buffer.** In keys mode the terminal hands over each key as soon as it's pressed, so a read returns one key's bytes, and a buffered reader just passes them on. The prototype (§3.4) reads keys through `stdin().lock()` and gets one read per key. The only care needed: anything left in the buffer when the mode changes belongs to the next read, so mode switches must use `TCSANOW`, not `TCSAFLUSH`, which discards unread input.

### 3.2 Keys mode, on a terminal

At the first `Terminal` operation, if standard input is a terminal, the runner saves the terminal settings and:

- turns off line editing and echo (`ICANON`, `ECHO`, `IEXTEN`), and `IXON` (so Ctrl-S and Ctrl-Q are keys) and `ICRNL` (so Enter is CR);
- **keeps `ISIG`, so Ctrl-C and Ctrl-\ still stop the program** (D1248), but disables the suspend character, so Ctrl-Z is `Ctrl 'z'`. (Suspending a program in keys mode would leave the shell's terminal in keys mode; speculative how each shell copes, so it's simply avoided.)
- switches to the alternate screen (`ESC [?1049h`), hides the cursor (`ESC [?25l`) and turns off line wrapping (`ESC [?7l`), so a line wider than the screen is cut off rather than wrapped.

At the next `IO` operation, and at exit, it undoes all of that. So `IO.print` after a game prints on the normal screen, below the shell prompt where the game started, and `IO.readLine` gets normal line editing. A program that never uses `Terminal` is never touched.

`draw` writes: cursor home (`ESC [H`), then each line followed by "clear to end of line" (`ESC [K`) and CR LF, then "clear to end of screen" (`ESC [J`), and flushes. There's no full clear, so the screen doesn't flicker.

**Reading a key.** One `readKey` decodes one key from the input bytes: a UTF-8 character, a control byte (CR or LF is `Enter`, 9 `Tab`, 127 or 8 `Backspace`, other bytes 1 to 26 `Ctrl` with a letter), or an escape sequence (`ESC [A` is `Up`, and so on, including the `ESC O` forms some terminals send). A sequence it doesn't recognise is skipped. **A lone `ESC` is `Escape` when nothing else arrived in the same read.** Terminals write an escape sequence in one go, so it arrives in one read; this is the cheap rule, and needs no timer. (Speculative in general: over a slow link a sequence could be split. The native runner could add a short `poll` wait later; the prototype shows `poll` works.)

**Size.** `TIOCGWINSZ` on standard output. If it fails or says 0 (as a fresh pseudo-terminal does, seen in the prototype), 80 by 24.

### 3.3 Without a terminal

Piped input and output must work too, for tests and for the playground.

- **Input that isn't a terminal:** `readKey` decodes keys from the bytes with the same decoder, and gives `None` at the end. So `printf 'jjk\033[Aq' | stitchwort run game.sw` plays a game. Invalid UTF-8 is `E-IO`, as for `readLine`.
- **Output that isn't a terminal:** no escape codes. `draw` writes each line followed by LF, then a line holding just a form feed (U+000C) to mark the end of a frame. A runner test compares that text with `Terminal.simulate`'s frames.
- **The playground** gets this for nothing: the input box's text is the key input, and the frames appear in the output, one after another. Keys pressed live in the page would need the machine to pause at `readKey` and resume when a key comes, which `run_main_fast` can't do today; that's later work with its own trigger. Arrow keys can't be typed into the box, so letter keys (`hjkl`) are the playground's way to move.

### 3.4 Native: confirmed by a prototype

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

Sending Ctrl-C (byte 3) instead: `signal SIGINT: terminal restored`, exit status 130, and the flags restored as above. Piped input (`printf 'k\033[Bq' | rawproto`) gave `[Char('k'), Down, Char('q')]` with no terminal calls. `rustix::termios::tcgetwinsize` returned 0 by 0 in the Python pseudo-terminal, which is why the fallback above exists.

**Dependencies: nothing new.** `nix` 0.31.3, with its `term`, `signal` and `poll` features, is already a normal dependency of `stitchwort-cli` through `rustyline` (`cargo tree -i nix -e features`), and its `tcgetattr`, `tcsetattr` and `SigSet::wait` are safe functions, so no `unsafe` is needed. For the size, `rustix` 1.1.5 is already in `Cargo.lock` (through `tempfile`); its `termios` feature gives a safe `tcgetwinsize`. No new crate means nothing new to fetch in the Nix build. `crossterm` wasn't tried: it isn't in the tree, and these two cover everything.

**Where the code lives.** `crates/rt` is also built for WebAssembly, so it can't call `termios`. The runner's `perform` gets the three `Terminal` operations through a small trait in `crates/rt/src/host.rs` (read a key, draw a frame, size, enter and leave keys mode). The pipe form (§3.3) is implemented there, generic over `BufRead` and `Write`, and is what the reference evaluator, the playground and the tests use. `crates/cli` implements the terminal form, under `cfg(unix)`.

### 3.5 Node (`run --js`): confirmed by a prototype

Node's own raw mode, `setRawMode`, doesn't fit:

- it belongs to `process.stdin` in the main thread, but the program runs in a worker, where "`process.stdin` … may be redirected by the parent thread" ([worker_threads](https://nodejs.org/api/worker_threads.html));
- in raw mode "Ctrl+C will no longer cause a `SIGINT`" ([tty](https://nodejs.org/api/tty.html#readstreamsetrawmodemode)), which goes against D1248.

Instead, the worker runs `stty -icanon -echo -iexten -ixon -icrnl min 1 time 0 susp undef` through `execSync` with standard input inherited (`stty` changes the terminal on its standard input), and keeps reading descriptor 0 as today. The launcher saves `stty -g` first and restores it on the worker's exit and on `SIGINT`, `SIGTERM` and `SIGHUP`. A scratch launcher and worker in a pseudo-terminal showed:

- keys arrived one read each, as natively (`[97]`, `[27,91,65]`, `[27]`, `[1]`, `[13]`, `[113]`), and the flags were restored after exit;
- **`process.exit(130)` in the main thread hung** while the worker was blocked in `readSync`, for over 20 seconds until killed. Restoring the terminal, removing the handler and sending `SIGINT` to itself again works: the process ended at once, killed by `SIGINT`, with the terminal restored;
- the Nix shell's GNU `stty` restoring `stty -g` output on macOS printed "unable to perform all requested operations" and exited with 1, but the flags were restored. The runner ignores `stty`'s exit status when restoring.

### 3.6 Windows

Out of scope. Nothing in the project targets Windows today. The native terminal form is `cfg(unix)`; elsewhere `Terminal` uses the pipe form.

## 4. Safety: putting the terminal back

| How the program ends | Native | `run --js` |
|---|---|---|
| Returns normally | The runner leaves keys mode before returning | The worker's exit handler restores |
| `Fail` unhandled, `E-IO`, `E-RESOURCE` | Same: these are `Err` results of `run_main`, so a guard value restores as the function returns | Same: the worker exits, the main thread restores |
| A Rust panic (an internal bug) | The guard's `Drop` restores (the workspace uses the default `panic = "unwind"`) | Not applicable |
| Ctrl-C, Ctrl-\, `kill`, closed terminal | The runner blocks `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` before starting any thread, and a waiting thread restores and exits with 130 (`SigSet::wait`, as in the prototype) | The main thread's handlers restore, then re-raise the signal |
| `kill -9`, a crash of the runner itself | Can't be caught. The user types `reset` | Same |

Ctrl-C works even while the program is busy computing and not reading keys, because `ISIG` stays on. That's the main reason for D1248: a `Partial` game loop with a bug that never reads a key can still be stopped.

**Piped input** never enters keys mode, so there's nothing to restore. **Output piped but input a terminal** (`stitchwort run game.sw > log`): keys mode is entered for input, and the pipe form is used for output.

## 5. A separate ability, or more `IO` operations? (D1246)

**Recommendation: a separate `Terminal` ability.**

- **The type says what a program needs.** A program whose type has no `Terminal` is guaranteed never to change the terminal's mode. The playground and tools can see from `main`'s type that it's a terminal program.
- **`IO.simulate` stays as it is**, with scripted lines and printed payloads. `Terminal.simulate` has scripted keys and frames. A program with both nests the two handlers, as with `IO` and `State` today. Adding keys and frames to `IO.simulate` would change its type for every existing test.
- **Mixing works.** `IO.print` and `IO.readLine` keep their meaning in a `Terminal` program; the runner switches modes between them (§3.2).

**The cost** is wiring: today `main`'s row is `{IO}` or `{Fail, IO}` (`MainRow` in `crates/rt/src/ir.rs`, the candidate annotations in `crates/driver/src/run.rs`, `perform` in `crates/js/src/run.rs`). Each learns a third ability. Adding operations to `IO` would be cheaper (as `readAll` was, in one commit), but it would put terminal modes into every `IO` program and into `IO.simulate`.

## 6. Randomness and time (D1249)

A roguelike needs a different dungeon each run. **Recommendation: one host operation, `IO.randomSeed: () → {IO} Nat`**, a fresh 64-bit number each run (from the operating system's random source natively, `crypto.getRandomValues` in Node and the browser). Everything else is pure: a small `Random` module in std (a seed in, a number and the next seed out), so dungeon generation is testable and replayable from a seed. `IO.simulate` gives the seed 0. A test that wants another seed calls the pure code with it.

- **Why not a seed argument?** `main` takes `()`, and `stitchwort run` passes no arguments today. Adding command-line arguments is a bigger change with its own design.
- **Why not the clock?** A turn-based game doesn't need it, and a clock as a seed is worse than a random seed. Time becomes worth adding with timed reads, for real-time games; neither has a trigger yet.
- **Why in `IO`, not its own ability?** It's general, not about terminals, and one operation doesn't justify another `main` row.

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
| **Bubble Tea (Go, the Elm architecture)** | `Update(Msg)` gets key messages | `View()` renders the whole UI after every update ([tea.go](https://github.com/charmbracelet/bubbletea/blob/main/tea.go)) | The library |
| **Lean 4** | `getLine` on a stream; no raw mode in core | `putStr`; streams can say `isTty` ([IO.lean](https://github.com/leanprover/lean4/blob/master/src/Init/System/IO.lean)) | Not applicable |

The low-level designs (Unison, OCaml `Unix`) give echo and buffering switches and leave restoring to the program. The libraries people use for games and TUIs (notty, vty, brick, Bubble Tea) all give the same three things: an event or key type, "draw this whole picture", and the library putting the terminal back. This proposal is that minimal set, with the runner in the library's place. Its `Key` is a subset of vty's.

## 8. Build plan

Each step is one lane.

1. **The std side.** `std/Terminal`: `Key`, `Terminal`, `Terminal.simulate`, registry built-ins for the ability and its operations (as `IO` and `Fail` have), and an `Ansi` module (`colour`, `bold`, `reverse`, `strip`). Tests: simulated runs (keys in, frames out, end of keys, nested with `IO.simulate`), and `strip` undoing each helper. A small example program, a walking `@` that `hjkl` and arrows move.
2. **The runners, pipe form.** `main` rows with `Terminal` (`MainRow`, the driver's candidates, `E-MAIN-TYPE`'s message, JS `perform`); the key decoder and frame writer in `crates/rt/src/host.rs`, used by the reference evaluator, the native runner and the playground; the same in the JS runner. Tests: decoder cases (every key, UTF-8, unknown sequences, lone `ESC`, end of input, invalid UTF-8); the example's output agreeing across `simulate`, `run`, `run --reference` and `run --js`; the playground running it with scripted keys.
3. **Native keys mode.** In `crates/cli`, `cfg(unix)`: entering and leaving keys mode as in §3.2, switching on `IO` operations, the size, the guard and the signal thread. Tests drive `stitchwort run` in a pseudo-terminal (the `pty` feature of `nix`, a crate already in the tree, as a dev-dependency) and check the flags after normal exit, `Fail`, `E-IO` and Ctrl-C.
4. **Node keys mode.** The `run --js` launcher and worker, as in §3.5. Tests: the same pseudo-terminal cases against `run --js`.
5. **`IO.randomSeed` and `Random`** (if D1249 is yes). The operation in every runner, seed 0 in `IO.simulate`, and a pure generator in std with its tests.

Steps 3 and 4 can run in parallel after 2; step 5 is independent of all of them.

## Decisions

**D1246. Make `Terminal` its own ability, separate from `IO`?**
Context: a separate ability shows in a program's type, keeps `IO.simulate` unchanged and gives terminal programs their own `Terminal.simulate`; the cost is teaching three runners a third `main` ability (§5). The alternative is three more `IO` operations, cheaper to wire, but every `IO` program and test then carries terminal operations.
Recommendation: **yes.**

**D1247. Programs draw whole frames (`draw: List Text → ()`), with no cursor, clear or write-without-newline operations?**
Context: it's the shape of Bubble Tea, brick, vty and notty; it makes tests compare screens as lists of lines, and works unchanged when output isn't a terminal and in the playground. The cost is no cheap single-cell updates (fine at roguelike sizes; the runner could diff frames later). Colour stays as ANSI text from pure helpers (§2).
Recommendation: **yes.**

**D1248. Keep Ctrl-C (and Ctrl-\) as "stop the program" in keys mode, rather than delivering them as keys?**
Context: with them kept, a game stuck in a loop can always be stopped, and the runner restores the terminal on the signal (both prototypes confirm it). The cost is that a program can't bind Ctrl-C; every other Ctrl letter, Ctrl-Z included, is a key. notty and Node's raw mode make the other choice.
Recommendation: **yes.**

**D1249. Add one host operation, `IO.randomSeed: () → {IO} Nat`, with randomness itself pure in std, and no clock for now?**
Context: a roguelike needs a different game each run; `main` takes no arguments, so a seed can't be passed in today. `IO.simulate` would give 0. Lean seeds its generator the same way. Time waits for real-time games (§6).
Recommendation: **yes.**

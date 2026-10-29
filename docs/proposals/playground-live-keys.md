# Stitchwort: live keys in the playground

**Status:** draft 1, 25 October 2026, for review (D1271, approved by Matt). Built (SW-520 and SW-521: pausable runs, the live run, the terminal pane); a scratch prototype ran first (§7). Decisions D1272 to D1275 are at the end.

Today the playground runs `Terminal` programs "with no terminal": the input box's text is the input, read in one go, and each frame comes out as lines with a form feed after it ([terminal-io.md](terminal-io.md) §4.5). So the roguelike can be replayed from typed-ahead letters, but not played. This note is about making it playable: keys pressed in the page reach the running program as they're pressed, and each frame replaces the last on a terminal-like grid.

One hard constraint: the playground is meant to become a **public static site**, files only, with no server logic. Everything below stays inside that.

Tags: **[source]** read in the code, **[ran]** run in a scratch prototype, **[web]** checked online (linked), **[inferred]** reasoned but not run, **[speculative]** a guess.

## 1. The recommendation in brief

- **Pause the machine instead of blocking the worker.** When the program asks for a key (`IO.readBytes`) and none has been pressed, the run *returns* to JavaScript with the waiting operation kept; when a key arrives, the worker pushes its bytes and the run goes on from where it stopped. This works because the machine's stack is already ordinary heap data (a `Vec` of frames), so stopping is returning from a loop **[source]**. A prototype of about 110 lines of Rust in `crates/rt` did it, and `terminal-walk.sw` played in headless Chrome, with 2 to 15 ms from key press to new frame **[ran]** (§7).
- **No special headers, no service worker, no reload, any browser.** The other route, `SharedArrayBuffer` with `Atomics.wait`, needs the page to be "cross-origin isolated", which needs two HTTP headers that GitHub Pages can't send (§3). It's doable on a static site, but costs a workaround or a choice of host; pausing costs neither.
- **The page gets a terminal pane:** a fixed 80 × 24 grid in a `<pre>`, a small interpreter for the few escape codes std's `Terminal` writes, and a keyboard handler turning key events into the bytes `Key.next` expects (§4). xterm.js isn't needed.
- **The runner side:** `IO.console` says "a terminal, 80 × 24" in a live run; keys mode switches the pane between the game's screen and the normal scrolling output, as the alternate screen does in a real terminal; `readLine` gets a line typed and edited in the pane, as a terminal's cooked mode does (§5).

## 2. How `readBytes` can wait: the options

The program runs in a web worker (`web/playground-worker.js`), on the bytecode machine compiled to WebAssembly, through `run_streaming` and `run_main_in` in `crates/web/src/lib.rs` **[source]**. Today the input is `Scripted`, a `BufRead` over the input box's text, so every read returns at once **[source]**. For live keys, a read must wait for the page. JavaScript in a worker can't wait for a message in the middle of a function: messages are delivered only once the current function returns. So either the worker blocks in a special way, or the WebAssembly run has to return and be resumed.

### 2.1 `SharedArrayBuffer` and `Atomics.wait`

The page and the worker share a buffer; `readBytes` calls into JavaScript, which sleeps in `Atomics.wait` until the page writes a key and calls `Atomics.notify`. This is how `stitchwort run --js` already reads standard input in its Node worker (`crates/js/src/run.rs`, "waiting with `Atomics.wait` when it isn't ready") **[source]**.

- **Support:** `SharedArrayBuffer` is in Chrome 68, Firefox 79 and Safari 15.2 (MDN's compatibility data, version 8.1.7 of 22 October 2026) **[web]**. `Atomics.wait` "is blocking and cannot be used in the main thread" ([MDN](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Atomics/wait)) **[web]**, which is fine: the program runs in a worker.
- **The catch:** "To use shared memory your document must be in a secure context and cross-origin isolated" ([MDN, SharedArrayBuffer](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/SharedArrayBuffer)) **[web]**. That takes two response headers on the page (§3).
- **Cost to us:** small in Rust: a `BufRead` whose `fill_buf` calls a JavaScript import that waits. No change to the machine.
- **Fit:** good, apart from the headers. The worker is blocked while it waits, so stopping a run still means terminating the worker, as today.

### 2.2 Pausing and resuming the machine

The run loop (`Runner::drive` in `crates/rt/src/run.rs`) is one Rust `loop` over a `focus` and a `Vec<Frame>`, and an `IO` operation is performed in `perform`, called from `route` **[source]**. Nothing of the program's own is on the Rust stack at that point: the module's header says the machine is "the stack-safe machine of docs/proposals/partial.md §7.4", and handlers capture "the frames above it" as heap values **[source]**. So when `readBytes` finds no input, the loop can keep the operation and its continuation in the runner and return; resuming is "perform it again, then carry on with the reply" (§7.1).

- **Support:** everywhere WebAssembly runs. Nothing new is asked of the browser.
- **Cost to us:** a change in `crates/rt` (the prototype is 113 lines added to `run.rs`), a live-run object in `crates/web` that owns the lowered program (the prototype leaked it, §7.1), and a new worker protocol. Native runners don't change: they never see "would block".
- **Fit:** the best of the five. The worker is idle between keys, so it can take messages (a key, "stop", "restart") without being killed. The run's per-stretch step budget already resets at each performed operation **[source]**, which is exactly the boundary a pause makes.

### 2.3 JSPI (JavaScript Promise Integration)

JSPI lets a WebAssembly call to an `async` JavaScript function suspend the WebAssembly stack until the promise settles: an import is wrapped in `WebAssembly.Suspending`, and the export in `WebAssembly.promising` ([V8 blog](https://v8.dev/blog/jspi)) **[web]**.

- **Support:** newer than I expected. MDN's compatibility data gives `WebAssembly.Suspending` and `WebAssembly.promising` as Chrome 137, Firefox 153 and Safari 27 **[web]**; webassembly.org's `features.json` agrees (Chrome 137, Firefox 153, Safari 27) and lists JSPI at phase 5 **[web]**. Safari 27 was released on 14 September 2026 and Firefox 153 on 21 July 2026 (MDN data) **[web]**, so older iPhones and iPads that can't update would lack it **[inferred]**.
- **Cost to us:** wasm-bindgen generates the JavaScript glue, and I found no wasm-bindgen support for JSPI (a search found nothing; **[speculative]** that none exists). We would have to patch the generated glue to wrap one import and one export, and the V8 post says "it is _not_ permitted to cause JavaScript code to be suspended by using JSPI" **[web]**, so the import must be called directly from WebAssembly, not through a JavaScript shim. That's fragile across wasm-bindgen upgrades **[inferred]**.
- **Fit:** works, but solves a problem our machine doesn't have: we can already return to JavaScript without help.

### 2.4 Asyncify

A Binaryen pass that rewrites the WebAssembly so it can unwind and rewind its own stack. Its author reports "the binary is around 50% larger on average", that "if the binary is 20% bigger, it tends to be at worst 20% slower", and that SQLite, with "one very large interpreter-like function", slowed "around 5x" ([Asyncify post](https://kripken.github.io/blog/wasm/2019/07/16/asyncify.html)) **[web]**. Our module is already 8.7 MB before `wasm-opt` (the prototype's build) **[ran]**, and its hot path is an interpreter loop, the worst case named. Works in every browser, but the price is high for something §2.2 does by returning.

### 2.5 Polling

- **Running in slices** (the worker runs a bit, returns to check its messages, runs again) is §2.2 with a timer added; pausing only at reads is simpler.
- **Synchronous `XMLHttpRequest` to a service worker** that holds the keys is a known trick for blocking reads without shared memory **[speculative]**: not checked in detail, because it needs a service worker as much as §3.2 does, plus a request per key.

### 2.6 Summary

| Option | Browsers | Headers or service worker | Change to our code | Worker between keys |
|---|---|---|---|---|
| `SharedArrayBuffer` + `Atomics.wait` | All current | Yes (§3) | Small, in `crates/web` | Blocked |
| **Pause and resume the machine** | **All** | **No** | **Moderate, in `crates/rt` and `crates/web`** | **Idle** |
| JSPI | Chrome 137, Firefox 153, Safari 27 | No | Patch wasm-bindgen's glue | Idle |
| Asyncify | All | No | Build step; about 1.5× size, slower | Idle |
| Sync XHR to a service worker | All with service workers | Service worker | Moderate | Blocked |

## 3. Cross-origin isolation on a static host

### 3.1 What it takes

The page must be served with `Cross-Origin-Opener-Policy: same-origin` and `Cross-Origin-Embedder-Policy: require-corp` (or `credentialless`) ([MDN, COEP](https://developer.mozilla.org/en-US/docs/Web/HTTP/Reference/Headers/Cross-Origin-Embedder-Policy)) **[web]**. `require-corp` then blocks cross-origin resources that don't opt in. The playground's only cross-origin resource is Google Fonts (`web/index.html` line 7) **[source]**, and both its CSS and font files answer with `cross-origin-resource-policy: cross-origin` (checked with `curl -I`) **[ran]**, so they would still load. `credentialless` isn't in Safari (MDN data: `version_added: false`) **[web]**, so `require-corp` would be the one to use.

### 3.2 Can a static host send them?

- **GitHub Pages: no.** The community request "Allow setting COOP and COEP headers in Github Pages" ([discussion 13309](https://github.com/orgs/community/discussions/13309)) is still open and unanswered; the only reply that looks like GitHub's, from July 2023, says "This is a scenario we would support with custom headers. No ETA at the moment", and comments as late as 25 October 2026 still ask for it **[web]**.
- **Cloudflare Pages: yes**, with a plain `_headers` file next to the site's files, up to 100 rules ([Cloudflare docs](https://developers.cloudflare.com/pages/configuration/headers/)) **[web]**. That's still a static site: a file of headers, not server code. Netlify has a similar `_headers` file **[speculative]**: not checked.
- **`coi-serviceworker`** adds the headers from a service worker "for situations in which you can't control the headers (e.g. GH pages)". It "will reload the page on the user's first load"; "it can't be loaded from a CDN: it must be served from your own origin"; and the page must be "served from HTTPS, or served from localhost" ([README](https://github.com/gzuidhof/coi-serviceworker)) **[web]**. Firefox used to disable service workers in private browsing, but that bug is fixed as of Firefox 138 ([bug 1320796](https://bugzilla.mozilla.org/show_bug.cgi?id=1320796), RESOLVED FIXED, target 138) **[web]**. Remaining costs: a reload on the first visit, a service worker sitting in front of every request to the site, and a site that half-works in any setting that blocks service workers **[inferred]**.

### 3.3 What this decides

Shared memory is possible on a static site, but only by choosing the host for its headers or adding a service worker and a reload. Pausing the machine has none of that, and it also leaves the page free to be embedded or opened from other sites, which `same-origin` opener policy and `require-corp` restrict **[inferred]**. So isolation tips the choice towards §2.2 (D1272).

## 4. The terminal on the page

### 4.1 The grid

A fixed **80 × 24** grid in a `<pre>`, one character per cell, re-rendered after each batch of output. The prototype does this in about 40 lines **[ran]**. A canvas isn't needed at this size, and text in a `<pre>` can be selected and copied.

`Frame.ansi` writes only: cursor home (`ESC [H`), the lines with "clear to end of line" (`ESC [K`) and CR LF between them, then "clear to end of screen" (`ESC [J`) ([terminal-io.md](terminal-io.md) §3.3) **[source]**. Keys mode adds the alternate screen, hidden cursor and no-wrap codes (`ESC [?1049h`, `ESC [?25l`, `ESC [?7l` and their reverses, §4.3 there) **[source]**. Colour is SGR (`ESC [ … m`) from `Std.Ansi` **[source]**. So the page interprets: CR, LF, `H`, `K`, `J`, `m` (reset, bold, reverse, the eight colours and their bright forms, default colour) and the `?…h`/`?…l` modes; anything else is ignored. The prototype showed the yellow `@` of `terminal-walk.sw` as a coloured cell **[ran]**.

**Why not xterm.js.** It is the complete answer (every escape code, focus, IME, a screen-reader mode), and cdnjs serves it (version 6.0.0 per cdnjs's API) **[web]**, but version 5.5.0's `xterm.min.js` alone is 290 KB, 67 KB gzipped (measured) **[ran]**, plus a stylesheet, for a program whose output std controls. Our interpreter covers everything std writes. If programs start writing arbitrary escape codes with `IO.write`, xterm.js is a drop-in later **[inferred]**.

### 4.2 Keys to bytes

On `keydown` in the focused pane, the page sends the bytes a terminal would (the table `Key.next` decodes, [terminal-io.md](terminal-io.md) §3.2) **[source]**, and calls `preventDefault` so the browser doesn't scroll or move focus:

| `KeyboardEvent.key` | Bytes |
|---|---|
| `ArrowUp`, `ArrowDown`, `ArrowRight`, `ArrowLeft` | `ESC [A`, `ESC [B`, `ESC [C`, `ESC [D` |
| `Home`, `End` | `ESC [H`, `ESC [F` |
| `Delete`, `PageUp`, `PageDown` | `ESC [3~`, `ESC [5~`, `ESC [6~` |
| `Enter`, `Tab`, `Backspace`, `Escape` | 13, 9, 127, 27 |
| Ctrl with a letter | 1 to 26 (but see D1274 for Ctrl-C) |
| A single printable character | its UTF-8 |
| Anything with Meta or Alt, function keys | nothing (the browser keeps them) |

Each key is pushed as **one read**, so `toIO`'s one-read rule (an `ESC` at the end of a read is `Escape`, §3.2 there) applies exactly as on a real terminal. The prototype sent `ArrowDown` and `ArrowLeft` this way and the `@` moved **[ran]**. Keys pressed while the program is busy queue up in order and are taken by the next read.

### 4.3 Focus

- The pane is a `tabindex="0"` element; clicking it or tabbing to it focuses it, and a visible outline shows that keys go to the program.
- While a run is live and the pane has focus, Tab goes to the program (a game may use it). So the page must say how to leave: a line under the pane such as "Keys go to the program. Ctrl-C stops it; Esc then Tab leaves the terminal" **[inferred]**. WCAG 2.2's "No Keyboard Trap" allows exactly this: if leaving needs more than the standard keys, "the user is advised of the method for moving focus away" ([W3C](https://www.w3.org/WAI/WCAG22/Understanding/no-keyboard-trap.html)) **[web]**. (The exact key is the lane's choice; "Esc twice" or Ctrl-] are other options.)
- When the run ends or is stopped, the pane stops taking keys, and Tab works normally.
- **Phones and tablets** have no physical keys, and focusing a `<pre>` doesn't open the on-screen keyboard **[speculative]**. A row of on-screen buttons (arrows and a few letters) would cover the roguelike; this is left out of the first build.

### 4.4 Size

`IO.console` reports the grid's size, 80 × 24, the same as `Terminal.simulate` uses, so a game sees the same screen in tests and in the page. On a narrow window the font shrinks to fit rather than the grid changing size **[inferred]**. Resizing isn't an event in `Terminal` anyway (§2 of terminal-io.md, "Left out").

### 4.5 Stopping and restarting

- **Stop** (the button, or Ctrl-C, D1274): while the program waits for a key, the worker is idle, so it simply drops the live run and answers "stopped". While it's computing, the page terminates the worker, as today (`runner.cancel()` → `worker.terminate()`, `web/index.html` line 912) **[source]**.
- **Restart** is Stop then Run. The compiled module is kept by the page, so a fresh worker starts quickly, as today **[source]**.

## 5. The runner side

### 5.1 What the host operations do in a live run

| Operation | Live run |
|---|---|
| `console ()` | Input and output are terminals; 80 × 24 |
| `keysMode True` | Writes `ESC [?1049h` (and the cursor and wrap codes), as natively; the page switches the pane to a fresh game screen and sends each key at once |
| `keysMode False` | Writes `ESC [?1049l`; the page goes back to the scrolling output, and to line input (§5.2) |
| `readBytes ()` | The keys pressed since the last read, as one read; if there are none, the run pauses until there are |
| `write t` | Appended to the output, flushed to the page |
| `print`, `readLine`, `readAll` | Leave keys mode first (D1260, as on every host) |

So the page learns about keys mode from the same escape codes a real terminal gets, in order with the output. The prototype's terminal didn't write them yet, and its final `IO.print` ("The @ stopped at column 1, row 2.") landed on the game screen next to the help line **[ran]**: with the codes, it would land in the scrolling output below, as natively.

### 5.2 `readLine` and `readAll` in a live run

Outside keys mode a real terminal is in "cooked" mode: it echoes what's typed, lets Backspace edit it, and hands over the line on Enter. The pane does the same: it echoes, edits, and pushes the line with its line ending on Enter. Ctrl-D on an empty line is the end of the input, as in a terminal **[inferred]**: `readLine` then gives `None`, and `readAll` returns what was typed.

**One trap for the build** **[source]**: `host::read_line` uses `read_until(b'\n')`, which takes bytes from the buffer before it reaches the end of it; if the end comes before a line ending and the read then says "would block", those bytes are lost. That can happen if keys were pushed in keys mode and the program then calls `readLine`. The live input must therefore say "would block" for a line read unless a whole line (or the end of input) is buffered, without taking anything. The prototype only ran `readBytes`, so this is untested **[inferred]**.

### 5.3 Limits and cancellation (D1275)

Today a run may take 15 seconds and print 256 KB in all (`RUN_SECONDS` and `MAX_OUTPUT`, `web/index.html` lines 775 to 777), and may read past the end of its input 10,000 times (`MAX_READS_PAST_END`) **[source]**. A game played for ten minutes, redrawing 1.7 KB per key, breaks the first two, and waiting for keys isn't time the program is using. So in a live run:

- **The time limit applies to each stretch between waits:** the page starts its 15-second timer when it sends a key and stops it when the run pauses again. A program stuck in a loop that never reads is stopped after 15 s, as today.
- **The output cap applies to each stretch too.**
- **Reading past the end** can't happen until Ctrl-D, so that limit stays as it is.
- **The machine's own step budget** is per stretch already: it "has its own step budget" between operations **[source]**, and resets at each performed operation and each tick.

### 5.4 When a run is live (D1273)

The input box stays, for scripted runs: they're reproducible, and they're how the existing examples and browser tests run. A second button, **Run in terminal**, starts a live run in the pane. A bundled project can say it runs live by default (the roguelike would). A program run with the plain Run button still gets "no terminal", exactly as now.

## 6. Build plan

Each step is one lane, stage-sized, running only the tests it names.

1. **Pausable runs in `crates/rt`.** `Runner` keeps a waiting operation (op, continuation, translations); `drive` can start from any focus; `LiveRun` (start, then `advance(input, output) → Waiting | Finished`), owning its program (an `Rc<Program>` in the machine, or the live run owning both, rather than the prototype's leak). Line reads that would block take nothing (§5.2). Tests, native, in `crates/rt`: a program reading keys with `readBytes` paused and resumed key by key gives the same output as one run with all the keys; the same for a partial `main` with handlers around partial code (the prototype's roguelike case); `readLine` across a pause keeps its bytes; the step budget still stops a loop that never reads. About the size of the prototype plus its tests.
2. **The live run in `crates/web` and the worker.** `start_live` and `start_live_project` returning a live-run object with `push`, `close` and `advance(sink)`; the live terminal of §5.1 (console 80 × 24, keys mode writing the screen codes); the worker's messages: start, key, close, stop. Tests: the existing native tests in `crates/web` style, with a recording sink stand-in, for the walk example and `readLine`.
3. **The terminal pane in `web/index.html`.** The grid and escape-code interpreter, the key table, focus and the "how to leave" line, cooked-mode line input, Run in terminal, Stop and Ctrl-C, the per-stretch timer and cap, a project manifest flag for "live by default". Tests: one browser test in `web/tests/browser.mjs` that plays `terminal-walk.sw` with arrow keys and checks the grid, and one for `readLine` typed in the pane.
4. **The roguelike bundled as live** (after the bundling lane lands). In the prototype the roguelike project failed to load in the WebAssembly build with `E-RESOURCE` ("it recursed more deeply than allowed", at `type State` in `Model.sw`) under the playground's limits **[ran]**, which looks like a checking limit the bundling lane will meet anyway, not something live keys cause **[inferred]**.

Lanes 1 and 2 could be one lane if small; 3 needs 2; 4 needs 3 and the bundling lane.

## 7. The prototype

### 7.1 What it changed (scratch, not committed)

- **`crates/rt/src/run.rs`:** `drive` became `drive_from(focus)`; the tail of `route` that performs an operation became `perform_and_continue(op, cont, back)`, which, if `perform` fails with `io::ErrorKind::WouldBlock`, keeps `(op, cont, back)` in a new `Runner::waiting` field and stops. A new `LiveRun` holds a `Runner<'static, 'static>`; its `advance` either starts the run or performs the waiting operation again, then continues the loop. Performing again is safe for `readBytes` because, before reading, it only flushes output, and `keysMode True` twice does nothing **[source]**.
- **`crates/web/src/lib.rs` and `project.rs`:** `LiveInput`, a `BufRead` whose `fill_buf` gives `WouldBlock` when no keys are buffered; `LiveTerminal` (console: terminals, 80 × 24); `start_live`, `start_live_project` and a `LiveSession` with `push`, `close` and `advance(sink)`. The lowered program and the terminal were `Box::leak`ed to get `'static` borrows.
- **A scratch page and worker:** the grid, the escape-code subset, the key table, one message per key.

The diff (359 lines added) is in the session's scratch space and isn't kept; lane 1 writes the real thing.

### 7.2 `terminal-walk.sw` in headless Chrome **[ran]**

A release WebAssembly build of the prototype, `wasm-bindgen --target web` into a scratch folder, served by a plain Node static server on port 9200 with **no COOP or COEP headers**, and a Node script driving headless Chrome over the DevTools protocol with real key events (`Input.dispatchKeyEvent`) on the focused pane, the keys `l`, `l`, ArrowDown, `j`, ArrowLeft, `q`:

```
first frame after 529 ms (page load, wasm compile, check, lower, run to first readKey)
isolated: false; states: ["waiting"]
############
#@.........#
...
-- after l: waiting, round trip 8.4 ms
#.@........#
-- after l: waiting, round trip 2.0 ms
#..@.......#
-- after ArrowDown: waiting, round trip 11.6 ms
#..........#
#..@.......#
-- after j: waiting, round trip 4.3 ms
-- after ArrowLeft: waiting, round trip 15.0 ms
#..........#
#..........#
#.@........#
-- after q: finished, round trip 7.7 ms
hjkl or arrows to move, q to stopThe @ stopped at column 1, row 2.
all round trips (ms): [8.4,2,11.6,4.3,15,7.7]
```

(Trimmed to the rows that change.) `isolated: false` is `self.crossOriginIsolated`: no shared memory was available or used. The round trip is from the page sending the key to the worker answering "waiting" after drawing the frame. The last line shows §5.1's point: without the keys-mode codes, the final `print` lands on the game screen.

### 7.3 The roguelike, natively **[ran]**

`terminal-walk.sw` is total, so its handler runs without the partial-handler frames. The roguelike's `main` is `{IO, Partial}` with `Terminal.toIO` and its own `Random` handler around partial code (`games/rogue/src/Rogue/Rogue.sw`) **[source]**, so a pause happens with captured handler frames on the stack. A scratch native test in `crates/web` loaded the eight program files of `games/rogue/src/Rogue`, started a `LiveRun`, and pushed `l`, `ESC [C`, `j`, `.`, `q` one per pause (release build, `cargo test --release -p stitchwort-web --lib prototype_live_roguelike`):

```
Waiting after 20.6ms: 1707 bytes written; first line "ESC[H ... ESC[K"
Waiting after 973µs: 1676 bytes written; ...
Waiting after 918µs: 1676 bytes written; ...
Waiting after 931µs: 1676 bytes written; ...
Waiting after 915µs: 1685 bytes written; ...
Finished after 1.06ms: 1723 bytes written; ...
last text: Some("You give up.\u{1b}[K\u{1b}[JYou gave up on level 1, on turn 4.")
test project::tests::prototype_live_roguelike ... ok
```

About 1 ms of work per key natively, and 1.7 KB per frame, close to terminal-io.md's guess of "about 2 KB per key press". In the browser the same project didn't load (the `E-RESOURCE` of §6 step 4), before any live code ran.

## Decisions

**D1272. Should live keys work by pausing the machine at a read and resuming it when a key arrives, rather than by `SharedArrayBuffer` and `Atomics.wait`?**
Context: shared memory needs two HTTP headers that GitHub Pages can't send; the workarounds are choosing a host that can (Cloudflare Pages' `_headers` file) or a service worker that reloads the page on the first visit. Pausing needs nothing from the browser or host, because our machine's stack is already heap data; the prototype did it in about 110 lines of Rust and played the walk example in headless Chrome without headers. The cost is a moderate change in `crates/rt`, used only by the playground.
Recommendation: **yes.**

**D1273. Should live runs be a separate "Run in terminal" button, keeping today's Run with the input box unchanged?**
Context: scripted runs are reproducible and the existing examples and browser tests use them; a live run needs a terminal pane and keyboard focus. The alternative is to run every program in the terminal pane and drop the input box. A bundled project such as the roguelike could start live by default either way.
Recommendation: **yes.**

**D1274. In the live terminal, should Ctrl-C stop the program, rather than reach it as the key `Ctrl 'c'`?**
Context: this matches D1248 for real terminals (Ctrl-C still stops a program in keys mode), and gives a keyboard way to stop a game stuck in a loop. The cost is that a program can't use Ctrl-C as a key in the page, as it can't natively either.
Recommendation: **yes.**

**D1275. In a live run, should the 15-second time limit and the 256 KB output cap apply to each stretch between key waits, instead of to the whole run?**
Context: a game is mostly waiting for the player, and redraws about 1.7 KB per key, so whole-run limits would end a normal game after 15 seconds or about 150 keys. Per stretch, a program that loops without reading is still stopped after 15 s, as today. Scripted runs keep their whole-run limits.
Recommendation: **yes.**

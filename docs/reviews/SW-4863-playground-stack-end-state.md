# SW-4863: why the playground runs out of stack on real proofs, and the end state

Measured 26 Nov 2026 (Fable lane), on `main` at 29ce187e5: Node 22.23 (V8 12.4), headless Chrome 158 and
Firefox 160 on macOS. Safari can't be run headless here, so nothing below is measured in WebKit. Follows
[SW-4857](SW-4857-playground-stack.md), whose figures it explains and in two places corrects.

## Summary

**The problem.** The playground can't check 2020 day 5's or 2024 day 22's proofs in Chrome (the
browser's own call stack overflows), and 2021 day 11's pass the guard by 2 KiB there and fail WebKit's.

**What is actually happening.** Checking these proofs is not what needs the stack.

- **Day 5 and day 22 overflow while printing a hover text.** With navigation on (the playground and the
  language server, not `stitchwort check`), the elaborator prints the type of every expression for hover.
  One type in day 22 mentions `Nat.iterate 2000 nextSecret buyer`, which as a value is 2,000 nested calls;
  one in day 5 holds 1,024 nested calls (from `List.range 0 (128 * 8)`). The printer prints such a term in
  full, three function calls a level, and only then finds the text is over its 240-character limit and
  prints it again ten levels deep. That first, discarded print is the whole of day 22's "604 KiB" and day
  5's "314 KiB". With the printer stopped at 200 levels (a one-line probe), day 22's proofs peak at
  96 KiB and day 5's at 73 KiB, and **Chrome 158 checks all six measured namespaces**, also with its
  slowest compiler tier forced and with the shipped `wasm-opt` step.
- **Day 11 is a real chain in the kernel's evaluator**, 100 long (the puzzle's 100 steps): a sum stuck on
  a sum stuck on a sum, each read by starting the evaluator again inside itself, nine calls and 3.4 KiB of
  WebAssembly stack a link. It fits Chrome's own stack with room to spare (it needs 174 to 224 KB of about
  480); what stops it is our guard (318 of 320 KiB in Chrome, and over WebKit's 192).
- **Chrome charges 8 bytes of its stack for every local variable of every WebAssembly function on the
  stack**, in code it has run only a few times, which is most of a checker's deep path. A worker has about
  480 KB. Our guard measures a different stack (the one in linear memory), and the two differ by a factor
  of 0.6 to 10 from one recursion to the next, in both directions: the guard lets the printer overflow
  Chrome, and all but refuses day 11, which Chrome has room for twice over.
- **The shipped build makes it worse.** `wasm-opt -Oz` puts back together the functions that SW-3128 split
  to keep frames small (`check_value` goes from 15 locals to 60, `check_tree` from 35 to 92, the printer's
  `go` from 9 to 42). That is why the real page overflowed sooner (268 KiB) than SW-4857's harness, which
  skipped that step.

**The end state I'd aim for** (section 5): display work never follows the size of a value; chains made by
computing (not by nesting in the source) are walked by loops, in the kernel's evaluator too; frames are
measured in the unit the browser charges and the build keeps them; and the browser's stack stops being the
limit at all, by running the checker on chained stacks through JSPI (JavaScript Promise Integration, in
Chrome since 137, Firefox since 153 and Safari since 27), which I measured giving 376 times the depth in
Chrome. The first three steps are small and are on that path; they are enough for the proofs measured.
Lowering Chrome's guard to 192 KiB (SW-4857's proposal) is not on it.

## 1. How it was measured

All scripts are in the lane's scratch folder (`SW-4863/n`, `SW-4863/jspi`, `SW-4863/site`); the method is
worth a task (section 7), since nothing in the repo could answer "which frames are on the browser's stack".

- **The browser's stack, frame by frame.** The playground's WebAssembly (built with
  `STITCHWORT_STACK_PROBE=1 STITCHWORT_GUARD=6000000`, as SW-4857's) runs in Node, which has Chrome's
  engine, V8, and unlike a Chrome worker lets the stack size be set: `node --stack-size=N`. `check_project`
  on one namespace, with the library's check cache loaded first. A bisection finds the smallest stack at
  which the namespace checks: **the engine stack the check needs**. One step below it, the `RangeError`'s
  stack trace (`Error.stackTraceLimit = Infinity`) lists every WebAssembly function on the stack at the
  overflow, by index and name.
- **Each function's frame.** `wasm-objdump -d` (wabt 1.0.41) on the same file gives, for every function,
  the bytes it takes from the stack in linear memory (the `__stack_pointer` adjustment in its prologue:
  the "wasm stack" the guard measures) and its number of locals.
- **The model for the engine's stack.** V8's first tier, Liftoff, keeps every value "in a register or …
  spilled to the physical stack frame" ([v8.dev/blog/liftoff](https://v8.dev/blog/liftoff)); around a
  call everything is in the frame. Estimating a frame as 8 bytes a local plus 48 and summing over the
  trace reproduces the stack size at the overflow within 1 to 3% wherever the code is cold (465 KiB
  estimated against `--stack-size=460`; 404 against 400; 333 against 330; 261 against 260; 200 against
  200; 895 against 880). So for cold code the estimate is the measurement, and "locals" is the number to
  watch. Hot code is recompiled by the optimising tier and takes less (day 11: 174 KB by default, 208 KB
  with `--liftoff-only`).
- **Chrome and Firefox.** SW-4857's harness (the real language server in a worker), on a build with the
  probe patch, in headless Chrome 158 with default tiering and with `--js-flags=--liftoff-only`; and a
  56-byte recursive WebAssembly function (16 locals) to measure each engine's stack with and without JSPI.

The probe patch is one line, not committed: `Printer::new` starts with `max_depth: Some(200)`
(`crates/core/src/pretty.rs`), so no print goes more than 200 levels deep.

## 2. Findings

### 2.1 What each namespace needs, and where

Unpatched build, default tiering, Node. "Engine stack" is the smallest `--stack-size` that checks the
namespace; "wasm stack" is the linear-memory stack of the frames on the trace.

| Namespace | Engine stack needed | At the overflow one step below | Levels | wasm stack on the trace |
|---|---|---|---|---|
| 2020 Day05.Proofs | 468 KB | hover printer, from `nav::not_unfolded` in `flush_navigation` | 1,024 | 334 KiB |
| 2024 Day22.Proofs | 888 KB | hover printer, from `value_for_message` in `flush_navigation` (after `signature`) | 1,994 | 624 KiB |
| 2021 Day11.Proofs | 174 KB | kernel evaluator, forcing a stuck sum, under `unify` | 100 | 340 KiB |

A Chrome 158 worker has about 480 KB (section 2.4), so day 5 is on the edge, day 22 is far over, and day
11 fits; that is the pattern SW-4857 saw without being able to say why.

The printer's cycle, a level (Day05 and Day22):

| Function | wasm stack, bytes | Locals | Engine estimate, bytes |
|---|---|---|---|
| `Printer::go_app` | 224 | 16 | 176 |
| `Printer::applied` | 64 | 14 | 160 |
| `Printer::go` | 16 | 9 | 120 |
| a level | 304 | | 456 |

The evaluator's cycle, a link (Day11), `force → force_now → run_on → resume → branch → stuck_tree →
nat_add::stuck_value → nat_add::stuck → native::view_with → force`:

| Function | wasm stack, bytes | Locals | Engine estimate, bytes |
|---|---|---|---|
| `value::resume` | 1,280 | 18 | 192 |
| `value::run_on` | 672 | 78 | 672 |
| `value::branch` | 304 | 24 | 240 |
| `nat_add::stuck` | 192 | 12 | 144 |
| `native::view_with` | 192 | 12 | 136 |
| `nat_add::stuck_value` | 144 | 10 | 128 |
| `value::force_now` | 96 | 5 | 88 |
| `value::stuck_tree` | 48 | 7 | 104 |
| `value::force` | 32 | 4 | 80 |
| a link | 2,960 (3.4 KiB measured, with the rest) | | 1,784 |

What makes these frames big, as far as the disassembly says: `resume` holds 1,280 bytes of values whose
address is taken with only 18 locals, which is large enums (frames, controls, values) moved through the
stack by value; `run_on` is the opposite, 78 locals, the machine's whole loop with its callees inlined,
which costs 624 bytes a level in Chrome's first tier though only one of its arms is the one recursing.
`go_app`'s 224 bytes are the `(String, Prec)` results and formatting temporaries of every notation it
tries. I did not trace individual locals back to source lines.

Elsewhere on the deep paths (none of them a peak once the printer is bounded): `check_tree` 1,712 bytes
and 35 locals, `matching::generalised_now` 2,160 and 47, `check_leaf_in` 736 and 36, `check::check_value`
672 and 15, `check::check` 400 and 19; `elaborate_namespace_untimed` has 139 locals but is on the stack
once.

The brief's "22 levels of `check_tree` at about 14 KiB a level" is day 5's native peak (SW-4854). It is
not what the WebAssembly build's peak is made of: there the elaboration of day 5's proofs needs under
112 KB of engine stack (below), and the printer is the other 356.

### 2.2 Why day 22 goes so deep (and day 5)

Neither depth comes from checking. `flush_navigation` (`crates/elab/src/nav.rs`) prints the type of each
expression and local noted for hover, as a value. `pretty::term_within` then:

1. prints the whole term at any depth (unless it has over 20,000 nodes);
2. if the text is longer than 240 characters, throws it away and prints again at depth 10, 9, …

A value such as `Nat.iterate 2000 nextSecret buyer`, with `buyer` a variable, is 2,000 nested calls, well
under 20,000 nodes, so step 1 recurses 2,000 levels to build a text that step 2 discards. Day 5's case
goes through `nav::not_unfolded`, which prints each parameter's type with `pretty::term`, which has no
limit at all. A term nested `n` levels deep can't print in fewer than `n` characters, so nothing deeper
than the character limit ever needs printing.

Running out of stack in that print is not an error (the printer writes `…` and the check goes on), so
under a guard the print simply stops at the guard. That is why these namespaces' "needs" were 314 and
604 KiB: they are how far the printer got, and with the guard at 320 KiB the printer runs until Chrome's
stack is gone: 320 KiB of wasm stack in the printer is about 480 KB of engine stack (ratio 1.5), which is
all a worker has.

Day 11's depth is real but is length, not nesting: `stepsFrom cavern 100` and its flash counts give a
sum whose second argument is a sum, 100 times. `nat_add::stuck` reads the second argument's head by
forcing it, which runs the machine again inside the first run. The evaluator is a machine with its frames
on the heap precisely so that length doesn't cost stack (docs/proposals/stack-safe-evaluation.md); this
path steps outside it once a link.

### 2.3 With the printer bounded

The probe build (no print deeper than 200 levels). The first two columns are Node; the last two are the
real language server in headless Chrome 158, where "deepest" is `phases().deepestKiB` for the namespace.

| Namespace | Engine stack needed, default tiering | With `--liftoff-only` | Chrome 158, default | Chrome 158, `wasm-opt -Oz` build, `--liftoff-only` |
|---|---|---|---|---|
| 2020 Day05.Proofs | under 105 KB | 112 KB | checks, deepest 73 KiB | checks, 73 |
| 2024 Day22.Proofs | under 105 KB | 112 KB | checks, 96 KiB | checks, 96 |
| 2024 Day13.Proofs | under 105 KB | 112 KB | checks, 132 KiB | checks, 132 |
| 2024 Day16.Proofs | 111 KB | 136 KB | checks, 156 KiB | checks, 156 |
| 2021 Day06.Proofs | under 105 KB | 88 KB | checks, 105 KiB (121 in `Day06` itself) | checks, 105 |
| 2021 Day11.Proofs | 174 KB | 208 KB | checks, 318 KiB | checks, 318 |

(105 KB was the first bisection's lower bound; the `--liftoff-only` run searched lower. For Day05, Day22
and Day13 the 112 KB is still the printer, now at its 200 levels, or the kernel's own checker: the
elaboration needs less.) Against SW-4857's table: Day22 604 → 96 KiB, Day05 314 → 73 KiB, the others
unchanged.

What the remaining peaks are made of (`--liftoff-only` traces): Day13, the kernel's `check` / `check_form`
/ `infer` / `infer_data`, about 100 levels, 140 KiB of wasm stack; Day16, the elaborator's `check` (53
levels) and then 120 levels of `Drop` for `Value` (`drop_glue` → `Values::drop` → `Rc::drop_slow`), a
recursion with no guard in it; Day06, the unifier (`same_calls` → `run_tasks` → `unify_step`, 74 levels).

### 2.4 The browser's stack, and why the guard is a poor stand-in

The 56-byte recursive function (16 `i64` locals, estimated 184 bytes a frame in Liftoff), in a worker:

| Engine | Levels, called directly | Levels under `WebAssembly.promising` (JSPI) |
|---|---|---|
| Chrome 158, `--liftoff-only` | 2,658 (about 480 KB) | 5,075 (about 910 KB) |
| Chrome 158, default (optimised after warm-up) | 63,833 | 121,835 |
| Firefox 160 | 163,029 | 163,824 |

- A Chrome worker has about **480 KB** of stack for WebAssembly in its first tier. The same function,
  once optimised, goes 24 times deeper: the tier matters more than anything we do, and a page can't
  choose it. Chrome compiles a function with the optimiser only when it "actually get[s] executed
  multiple times" ([v8.dev/blog/wasm-dynamic-tiering](https://v8.dev/blog/wasm-dynamic-tiering)), and a
  check's deepest path is typically code running for the first time, so the first tier is the case to
  design for. Firefox has far more room; nothing measured comes near it.
- The ratio of engine stack to wasm stack, by recursion (first tier): kernel evaluator 0.6, elaborator's
  `check` about 0.6, printer 1.5, `Drop` of values about 10 (304 bytes of engine stack a level for 32 of
  wasm stack). A guard in wasm-stack bytes is therefore wrong by an order of magnitude between the extremes,
  whatever number it is given: at 320 KiB it lets the printer overflow Chrome, and is 2 KiB from stopping
  day 11 with half of Chrome's stack unused.
- SW-4857's prediction that a 192 KiB guard would refuse Day05 and Day22 does not hold: their figures were
  the printer's, and the printer stopping at a guard is not an error. A 192 KiB guard would in fact have
  let both check (the printer would stop at about 290 KB of engine stack, as rustc builds it), which shows how accidental the
  current behaviour is. It would still refuse Day11 (318), and with the printer bounded there is no
  measured reason for it in Chrome.

### 2.5 The shipped build undoes the frame splitting

`web/build.sh` runs `wasm-opt -Oz`, which SW-4857's harness and this lane's first builds did not. Binaryen
inlines every function that has one caller, whatever its size (`--one-caller-inline-max-function-size`,
default unlimited), which is exactly the functions marked `#[inline(never)]` to keep a recursion's frame
small.

| Function | Locals, rustc's output | After `wasm-opt -Oz` | After `wasm-opt -Oz -ocimfs=30` |
|---|---|---|---|
| `Printer::go` | 9 (and `go_app` 16, separate) | 42 (`go_app` and the other kinds inside it) | 9 (and 15) |
| `check::check_value` | 15 | 60 | 15 |
| `elab::check_tree` | 35 | 92 | 35 |
| `check::check` | 19 | 24 | |
| `value::branch` | 24 | 32 | |
| `value::run_on` | 78 | 79 | 78 |

Engine stack needed, probe build, Node `--liftoff-only`: Day16 136 KB as rustc built it, **160 KB after
`-Oz`**, 128 KB after `-Oz -ocimfs=30`; Day05 112, 128, 112; Day11 208, 224, 216. The file grows from
16.6 MB to 18.4 MB uncompressed (with the name section in both; rustc's output is 20.8 MB).

### 2.6 Engine features

- **JSPI (JavaScript Promise Integration).** Supported in Chrome and Edge 137 (May 2025), Firefox 153
  (July 2026) and Safari 27 (September 2026); Baseline "newly available" since 14 Sep 2026
  ([web-features explorer](https://web-platform-dx.github.io/web-features-explorer/features/wasm-jspi);
  [Mozilla's intent to ship](https://groups.google.com/a/mozilla.org/g/dev-platform/c/8cOxM-dWaNs)).
  Measured present in Chrome 158's and Firefox 160's workers. An export wrapped in
  `WebAssembly.promising` runs on a stack of its own. On its own that buys a constant: 1.9 times the
  worker's stack in Chrome, nothing in Firefox (table above). V8 describes these stacks as fixed-size
  today, with growable ones a goal ([v8.dev/blog/jspi-newapi](https://v8.dev/blog/jspi-newapi)).
- **JSPI as a chain of stacks (measured, new).** A function deep in a recursion can call an import made
  with `WebAssembly.Suspending` whose JavaScript calls a `promising` export: the rest of the recursion
  then runs on a fresh stack, and the caller resumes when it returns. This is `stacker::maybe_grow` built
  from JSPI. With a new stack every 2,000 levels, the test function reached **1,000,000 levels in Chrome
  158 with `--liftoff-only`, against 2,658 directly (376 times), in 55 ms** (500 stacks; 4,000,000 levels
  failed). Firefox 160, with a new stack every 100,000 levels, reached 4,000,000 levels (40 stacks)
  against 163,029 directly (24 times); with one every 2,000 levels, 50 stacks worked and 500 did not, so
  it caps the number of live stacks somewhere between. The stack in linear memory is untouched by this, one contiguous 8 MiB as now, so the guard goes on measuring it.
  Not measured in Safari.
- **The stack-switching proposal** (core WebAssembly instructions for switching stacks, which would let
  Rust code do this without JavaScript) is at phase 3 and not shipped in any browser
  ([WebAssembly/proposals](https://github.com/WebAssembly/proposals),
  [WebAssembly/stack-switching](https://github.com/WebAssembly/stack-switching)). Not something to plan on.
- **Nothing sets a worker's stack size.** `--js-flags=--stack-size` does nothing in Chrome's workers
  (SW-4857), and there is no web API for it. The main thread has more, and must not run a checker.
- **Nothing sets the tier.** No option of `WebAssembly.compile` asks for the optimiser. Warming functions
  up by calling them is the only lever, and it is a hack that depends on the engine's thresholds.

## 3. The options

"Buys" is measured unless marked estimated.

| Option | What it buys | What it costs | Native, kernel | End state or step |
|---|---|---|---|---|
| **P. Bound the printer by its output**: a print for a message or hover stops descending where the text can no longer fit its limit; `not_unfolded` gets a limit | Day22 604 → 96 KiB, Day05 314 → 73; engine need 888 and 468 KB → about 112. All six namespaces check in Chrome | A small change in `pretty.rs` and `nav.rs`. A hover type deeper than the limit shows `…` inside, as one longer than 240 characters already does | Native: stops building and discarding huge texts in the language server (not timed). Kernel: none, the printer is outside it | **End state** for display work |
| **W. Keep the frame splits in the shipped build**: `wasm-opt -Oz -ocimfs=30` (or the functions named with `--no-inline`) | Day16's engine need 160 → 128 KB (20%); `check_value`'s frame in Chrome 528 → 168 bytes, `check_tree`'s 784 → 328 (estimated from locals) | 1.8 MB more WebAssembly before compression (11%) | None | End state for the build; one line |
| **a. Shrink frames in the hot recursions** (`resume`'s 1,280 bytes, `run_on`'s 78 locals, `check_tree`, `generalised_now`) | Estimated: boxing `resume`'s big values would take day 11 from 318 to about 200 KiB of wasm stack (just over WebKit's guard) and little off its engine need; splitting `run_on`'s recursing arm from its loop would take about 500 bytes of engine stack off each link (30%) | Per-function work, found with the method of section 1; small diffs. `resume` and `run_on` are kernel evaluator code, so each change is reviewed as one | Native frames shrink too. Kernel: no rule changes, same structure | A step. Constant factors: each buys tens of percent, and the next proof can be twice as long |
| **b. Loops for the chains that computing makes**: `nat_add::stuck` reading a sum of sums; `Drop` for `Value`; (the printer's right-nested calls, if P were not done) | Day11's 100 links → a constant (estimated: its peak falls to the elaborator's, about 130 KiB). Removes the unguarded `Drop` recursion (Day16: 120 levels today, unbounded in principle) | The stuck-sum loop is a change to a kernel rule's implementation (R3/R4 in docs/core.md): same rule, read iteratively, with `docs/core.md` and a soundness review. `Drop` as a loop is a known pattern, already the policy (deep-input.md rule 1) | Native: same benefit, and `Drop` can't report an error on any platform. Kernel: slightly more code in the trusted base, no new rule | **End state** for length: it is rule 1 of deep-input.md applied to values, not only to source |
| **c1. JSPI, plainly**: run each check under `WebAssembly.promising` | 1.9× in Chrome, 1.0× in Firefox | The worker's calls become asynchronous | None | Neither: a constant, engine-specific |
| **c2. JSPI as a chain of stacks**: at a guard site, every so many KiB of wasm stack, continue on a fresh engine stack | 376× the depth in Chrome's first tier, 24× in Firefox (as far as tested). The engine's stack stops being the limit; the guard becomes a policy number, as natively | The checker's entry points in the worker become asynchronous; one hand-written import and export beside wasm-bindgen's (a JavaScript frame between WebAssembly and the suspending import is not allowed); a rule for when to switch (wasm-stack bytes since the last switch, small enough for the worst ratio); browsers before 2025-26 fall back to today's guard. Unknown: Safari's behaviour, the cap on live stacks (over 500 in Chrome, between 50 and 500 in Firefox) | Native: untouched (the switch compiles away). Kernel: one call in `Budget::nesting`'s slow path, no logic | **End state** for nesting in the browser, if a prototype holds up |
| **c3. Core stack switching, a bigger worker stack, choosing the tier** | Nothing available | | | Not available |
| **d. Splitting work across calls, CPS, trampolines** for the elaborator and the kernel's checker | Would remove the engine stack from nesting too | Rewrites `check`, `check_tree`, `unify`, `infer` (tens of thousands of lines of mutual recursion) into machines; the kernel's checker would stop reading like its rules | Slower natively (heap frames for every level); a much larger trusted base | Not recommended. The evaluator already is a machine, which is where length lives; nesting is bounded by what people write (53 levels at most here) |
| **e. A different shape for the value** (keep `Nat.iterate 2000 f x` folded when showing it) | Nicer hover text | The printer shows values, and folding is `quote_shown`'s job; this case computes because the count is a literal | | A possible refinement after P; not needed for the stack |
| **g1. A small stack allowance for navigation's prints** (say 64 KiB, in `flush_navigation`) | A second bound on display work that doesn't depend on P being complete | One line | | A step, belt and braces with P |
| **g2. Catch the engine's overflow and report it** (SW-4862, in progress) | The truth about the engine's stack, whatever the tier | A restart and a re-check | | End state as the backstop under any design |
| **g3. Lower Chrome's guard to 192 KiB** (SW-4857's proposal) | Nothing these proofs need once P is in | Refuses Day11, which Chrome has room for | | **Leads elsewhere**: it tunes the stand-in instead of fixing what it stands in for |

## 4. What I would not do

- **Tune the guard to the printer.** Any number is wrong for some recursion by a factor of ten (2.4).
- **Warm functions up** to get them optimised, or count on the optimising tier: a design that only works
  when the engine has decided the code is hot fails on the first check of a new proof.
- **Rewrite the elaborator or the kernel's checker as machines** (d). The cost is the kernel's
  readability, and c2 gets the same result from outside.
- **Asyncify** (Binaryen's transform that can unwind and rewind the stack): rewinding re-enters every
  frame, so it gives no extra depth, and it grows the code.

## 5. Recommendation

**End state**, in four statements:

1. **Display work is bounded by what it will show.** No print for a message, goal or hover recurses, or
   allocates, in proportion to a value's size (option P, with g1).
2. **Length never costs stack, for values as for source.** deep-input.md's rule 1 covers chains made by
   computing: the kernel's native rules read a chain with a loop, and `Drop` of terms and values is a
   loop (option b).
3. **Frames are measured in the browser's unit and the build keeps them.** A task reports, for a
   namespace, the engine stack it needs and the frames at the peak (section 1's method); the shipped
   build doesn't re-inline what was split (option W); hot frames are trimmed where the table says (a).
4. **In the browser the engine's stack is not the limit.** The checker continues on a fresh stack as it
   goes deeper (option c2), so the playground's limit is the guard, a policy number in bytes of wasm
   stack as natively, and a `RangeError` is a bug to catch (g2), not the normal way to run out.

**Order of steps.** Each is a ticket; 1 to 3 are small and all on the path.

1. **Bound the printer (P, g1).** Sonnet or Opus, core printer and `nav.rs`; test: a hover type over
   2,000 nested calls prints without recursing past the limit, and Day22.Proofs' deepest falls under
   128 KiB in the browser test. This alone makes the measured proofs check in Chrome.
2. **`wasm-opt` keeps the splits (W).** One line in `web/build.sh`, plus a check in the build that named
   functions (`Printer::go_app`, `check_value`, `check_tree`) still exist with about their locals.
3. **Measure, then set the guards.** `task stack:wasm` (the scripts of section 1: Node bisection, the
   overflow's trace, frames from the disassembly); one whole-AoC run of it on Overmind to list every
   namespace's engine need and wasm peak; then choose Chrome's and WebKit's guards from that list.
   SW-4857's 192 KiB for Chrome waits for this, and I expect it to be unnecessary.
4. **The kernel's stuck-sum chain (b)**, as an Opus design-and-implementation lane with a soundness
   review, since it touches how a kernel rule is computed; and `resume`'s frame (a) while there. This is
   what Day11 needs to pass WebKit's guard and to stop being 2 KiB under the 320 KiB one.
5. **`Drop` for `Value` and `Term` as loops (b)**, under deep-input.md's existing rule; SW-1966's lint
   should be listing these.
6. **Prototype the chain of stacks (c2)**: a probe build in which `Budget::nesting` switches stacks, run
   on Day11 with a 64 KiB switch interval in Chrome, Firefox and (by Matt, by hand) Safari. Decide on the
   result.

Steps 1 and 2 are quick wins that are also the end state for their part. Step 3 gives the numbers the
later ones are judged by. Steps 4 to 6 are independent of each other.

## 6. Decisions for Matt

Numbered within this note; the orchestrator gives them D numbers.

1. **The chain of stacks through JSPI as the browser's end state** (step 6, option c2): prototype it?
   It makes the playground's depth limit ours to set, and makes the worker's checking calls asynchronous
   and dependent on a browser feature from 2025-26, with today's guard as the fallback. [rec: yes, as a
   prototype after steps 1 to 3, then decide on its measurements]
2. **A loop in the kernel for sums of sums** (step 4): the rule is unchanged, its implementation gains a
   loop, and it goes through a soundness review. The alternative is frame trimming only, which helps Day11
   by tens of percent and leaves the chain. [rec: yes]
3. **Hover text**: a type nested deeper than its character limit shows `…` for the inner part instead of
   being printed in full first, and the unfolded-`Not` hover gets the same 240-character limit as the
   main one (today it has none). User-visible but small. [rec: yes; the orchestrator's call unless Matt
   wants to see it]

## 7. Findings worth tickets

- **`pretty::term_within` prints in full before measuring** (step 1); `nav::not_unfolded` prints with no
  limit. Also a time and memory cost natively, not measured here.
- **`web/build.sh`'s `wasm-opt -Oz` re-inlines `#[inline(never)]` functions** (step 2). SW-4857's and
  SW-3128's browser figures were taken on builds without `wasm-opt`, so they understate the shipped page.
- **`task stack:wasm`** (step 3): `task stack:peak` reads native frames, which don't predict the browser
  (it named `check_tree` for Day05; the browser's peak was the printer, which `check` doesn't run).
- **`Drop` for `Value` recurses, unguarded** (`drop_glue::<Value>` → `Values::drop` → `Rc::drop_slow`,
  120 levels in 2024 Day16.Proofs): deep-input.md rule 1.
- **`nat_add::stuck` forces its argument by re-entering the machine** (step 4): the one place found where
  the evaluator's length costs stack.
- **`crates/web/build.rs`'s comment** attributes the guard's history to recursions by their wasm-stack
  bytes; it should say that Chrome's first tier charges by locals and point at the task.
- **SW-4857's table** should carry a note that the Day05 and Day22 rows measure the hover printer.

## 8. What this doesn't cover

- Safari and WebKit: nothing measured. Its worker stack (about 297 KiB of wasm stack on nested
  applications, SW-4849) and its JSPI behaviour need a run by hand.
- Only SW-4857's six namespaces. Other AoC proofs, the roguelike and the book may have peaks of other
  kinds; step 3's whole-project run is how to find them.
- Node's V8 is 12.4 and Chrome 158's is newer; the frame model was fitted in Node and agrees with
  Chrome's overflow points (480 KB by the test function; SW-4857's Day22 overflows at 301 to 331 KiB of wasm stack
  are 450 to 500 KB at the printer's ratio), but Chrome's frames were not read directly.
- I did not find which expression's hover in Day05 holds the 1,024 nested calls, only that it is printed
  from `not_unfolded` and that the namespace's types mention `(List.range 0 (128 * 8)).filter …`.
- The estimates for options a and b are from frame sizes, not from builds with the change.

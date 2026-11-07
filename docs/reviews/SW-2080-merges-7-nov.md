# Review of three merges of 7 Nov 2026 (SW-2080)

A fresh-eyes review, from the code only, of:

- `d353951d6`, **SW-1885**: the pin table (`crates/core/src/pins.rs`);
- `c66990756`, **SW-1916**: the `"""` pre-scan uses the lexer (`crates/syntax/src/lexer.rs`);
- `ef1c7d459`, **SW-1820**: language server panic recovery, stage 1 (`crates/lsp/src/lib.rs`).

Read only: nothing was built or run. Line numbers are those on `main` at
`36dbd371e`.

## Summary

All three merges do what they claim, and I found nothing unsound and no
reachable crash. **SW-1885** closes the soundness hole it was for. Every
pinned declaration is checked before its native, its rules or `natNeq` are
bound. It is checked again on a check-cache replay, because replay goes
through `bind_builtin_def` too. No shipped binary calls the pin-skipping
paths. **SW-1916** removes the panic properly: the pre-scan and the main
pass now use the same code to find a `${…}`'s end, and the cost stays
linear. **SW-1820** catches what it says it catches, and restarts workers
cleanly. The findings are all low or medium: comments that claim more than
the code does, one ordering hazard that can't be reached today, a pin check
that no table enforces, and tests that stop short of what they name.

Top five recommendations:

1. **Check every pin in one place** (P1, medium). Do it in
   `bind_builtin_def` for every builtin with a pin, and keep
   `register_native`'s own guard. Then a pin added later can't be silently
   unchecked, and SW-1991's runtime pins have a place to be checked.
2. **Make the search-panic test panic where a real one would** (S1,
   medium). That is inside a search, after the kept session has been taken
   out, not before `search.run`. Make its failure an assertion, not a
   120 s timeout.
3. **Correct `Main::request`'s safety argument and fix the ordering under
   it** (S2, low). Some handlers do change state (`queue_search`). Build
   the job before inserting it into `pending`.
4. **Fix the pin comments that overclaim** (P2, low). `pinned_hashes.rs`
   can't "list every stale one at once", because its session refuses at the
   first. `pins.rs` isn't the only place in the source with pins.
5. **Decide whether bidi controls in comments and text get a warning**
   (L3, D2970). SW-1916 names them only where they're already errors.

Findings by severity: high 0, medium 2, low 9.

## Findings

| # | Merge | Severity | Confidence | Size | Finding |
|---|---|---|---|---|---|
| P1 | SW-1885 | medium | high | S–M | No single place checks every pin: each registration function checks its own builtins, and nothing ties `PINS` to those functions |
| S1 | SW-1820 | medium | high | S | The search-panic test panics before the search starts, so the case the restart exists for is never exercised; a failure is a 120 s timeout |
| P2 | SW-1885 | low | high | S | Comments that overclaim: `pinned_hashes.rs:41` ("lists every stale one at once") and `pins.rs:21` ("nowhere else in the compiler's source") |
| P3 | SW-1885 | low | high | S | The fallback (`stale_pins_fall_back`, `Session::with_prelude_falling_back`) ships in release builds, unlike `register_native_unpinned` |
| P4 | SW-1885 | low | high | S | The "a second definition for the same native" refusal is untested; its message names the wrong native in the other case |
| S2 | SW-1820 | low | high | S | `Main::request` says handlers don't change state; `queue_search` does, and a panic between its `insert` and `send` would leave a request unanswered |
| S3 | SW-1820 | low | high | S | The catch covers only `search.run`: a panic elsewhere in `run_search` leaves the request unanswered and `running` incremented |
| S4 | SW-1820 | low | high | S | Wrong docs: in the playground, `catch_unwind` does nothing (wasm aborts); `Inline::tick` drops `run_search`'s "didn't survive" flag; `Faults` "a relaxed load" |
| L1 | SW-1916 | low | high | S | A `--` comment inside a `"""` text's `${…}` gives "a `${…}` … stays on one line", though it is on one line |
| L2 | SW-1916 | low | medium | S | `invisible` misses format characters that show as nothing (U+2061–U+2064, U+180E, U+034F, U+061C, tags) |
| L3 | SW-1916 | low | high | S–M | Bidi controls and zero-width characters pass silently in comments and text literals (Trojan Source): D2970 |

Comments that narrate history, a pattern across all three merges, are listed
under each merge rather than as findings of their own.

## SW-1885: the pin table

### P1. No single place checks every pin (medium, high, S–M)

The pin check is called from four registration functions:
`native::register_native` (`native.rs:404`), `register_nat_neq`
(`native.rs:522`), `float::register_def` (`float.rs:684`) and
`float::register_data` (`float.rs:589`). `bind_builtin_def`
(`elab/src/lib.rs:3019`) reaches these through a `match` on the builtin.
I checked all 23 entries of `PINS` today, and each reaches one of them: the
nine Nat natives through `Native::ALL`, `NatNeq` directly, the twelve float
definitions through `PINNED_DEFS`, and `Float` through `bind_builtin_data`.

Nothing enforces that, though. `every_native_is_pinned` checks one
direction only: every native has a pin. The other direction is unchecked: a
pin that no registration function checks is never checked. For example,
SW-1991 will add pins for the runtimes' natives and the rewrites, which
have no kernel registration function. Each of those needs a new call site,
and if one is forgotten the pin is decoration. `pinned_hashes.rs` would
still pass, because it compares hashes rather than asking whether anything
refused. `backend-trust.md` §3.2 put the check "at binding", in
`registry::bind_def` and `bind_data`, for this reason.

**Recommend:** in `bind_builtin_def` and `bind_builtin_data`, call
`pins::check_def` / `check_data` for every `b` with `pins::pin(b).is_some()`,
before the `match`. The fallback test goes in the same place. Keep the
calls inside `register_native` and `register_nat_neq` too, so that the
kernel's guard doesn't depend on the elaborator. Hashes are memoised, so
checking twice costs nothing. This belongs at the start of SW-1991.

### P2. Comments that overclaim (low, high, S)

- `crates/driver/tests/library/pinned_hashes.rs:41`: "a stale one refuses
  the library, so this is a second line that lists every stale one at
  once." It can't do that. `every_binding_by_hash_applies_to_the_library`
  builds its session with `Session::eager_for_stack`, which has no
  fallback, so a stale kernel pin refuses at the first one and the test
  panics in session start-up, before `bindings` runs. `backend-trust.md`
  §3.3 item 1 wanted this test to list every stale pin. Either build its
  session with `stale_pins_fall_back` set, as `examples/pins.rs` does, or
  reword the comment to send the reader to `task pins:show`.
- `crates/core/src/pins.rs:21`: "The pins live here … and nowhere else in
  the compiler's source." Other pins remain: `chars.rs` (compact text, a
  kernel representation), `rt/natives.rs` and `driver/src/float_gate.rs`
  still hold 64-digit pins. The next sentence covers the runtimes'
  (SW-1991), but not `chars.rs`. Say "the kernel's natives' pins".
  SW-1991 already moves `chars.rs`.
- `backend-trust.md` §3.3 says `nat_add_is_the_pinned_declaration` and
  `the_float_bindings_are_the_pinned_declarations` become redundant. They
  were kept and updated instead. That's harmless, but they now test what
  start-up already refuses.

### P3. The fallback ships in release builds (low, high, S)

`Options::stale_pins_fall_back` (`elab/src/state/options.rs:76`),
`Session::with_prelude_falling_back` and `try_with_prelude_falling_back`
(`driver/src/driver.rs:498`, `:505`) are `pub` and `#[doc(hidden)]`, with no
feature gate. `register_native_unpinned` sits behind `test-bypass`, which
only `stitchwort-dev-features` enables. I found no shipped caller: the
only callers are the extract test and `crates/driver/examples/pins.rs`.

I checked that this isn't a soundness matter. In the fallback, a stale
definition is bound in the registry but gets no native. R3 and R4 stay off
because `nat_add::register` asks `pins::holds`. Anything that depends on a
stale definition hashes differently, so it is stale too and also falls
back. The kernel then computes with the definitions as written, which is
always sound. Leaving the option out of the options fingerprint
(`options.rs:121`) is safe too: a changed prelude changes the hashes the
cache entries are keyed by, and replay checks the pins again.

So the cost is only that a release build carries a switch that turns off
natives, with nothing to stop a future caller. **Recommend:** gate the
option and both constructors behind `test-bypass`, as
`register_native_unpinned` is. The example and the extract test build with
dev-features, so both keep working.

### P4. The second-registration refusal is half tested (low, high, S)

`register_shaped` (`native.rs:498`) refuses in two cases: `id` already has a
native, or `native` already has a definition. Two tests cover it, and
neither reaches the second case. The core test (`glue.rs:192`) registers
the same `id` twice. `a_native_is_registered_once` registers `Nat.sub` as
`Native::Add`, which the pin refuses first. The case F16 was about, two
definitions for one native, has no test. Also, when `id` already has a
*different* native, the message "`Nat.add` is bound to a native already"
names the new native, not the definition's. **Recommend:** a core test
using `register_native_unpinned` on two different definitions for one
native, and a message for each case.

### Comments

`nat_add.rs:211-212` ("Its native has refused the library already, unless a
test let stale pins fall back") is true, because `Nat.add` binds before
`Nat.addSucc`. It would read better as the invariant: "`Nat.add` is bound
before `Nat.addSucc`, so a stale one has refused the library already, except
in a falling-back session." No other comment narrates the change.

### Checked and sound

- **Every way to register a native goes through the pin check.**
  `register_native` and `register_nat_neq` check the pin first. Their only
  callers are `bind_builtin_def` and two tests. The only unpinned path,
  `register_native_unpinned`, is behind `test-bypass`, and only
  `stitchwort-dev-features` enables it. That crate is a dev-dependency, and
  the flake package and the browser bundle don't use it.
- **Natives aren't registered anywhere else.** `natives.insert` and
  `native_defs.insert` appear only in `register_shaped`. JS's and rt's
  `natives.insert` are other tables (SW-1991). Check-cache replay
  (`cache/mod.rs:2791`) calls `bind_builtin_def`, so it checks the pins
  again.
- **Rewinding is consistent.** `native_defs` is rewound with `natives`
  (`native.rs:263`), and `nat_neq` through `BuiltinsMark`. So after an
  undo, "registered once" doesn't refuse a re-registration. The memoised
  hashes are rewound too (`caches.rs:27`), so a reused `DefId` can't keep
  an old hash.
- **A hash that can't be computed refuses.** If hashing runs out of stack
  or the definition isn't final, `check` refuses with "can't be computed".
  It never skips the check (D2543).
- **The pins cover what the natives assume.** The `Nat` data type is
  covered by `Nat.add`'s hash (its type refers to it), `Bool` by `leq`'s
  and `Decidable` by `decEqNat`'s. The theorem natives (`EqNatRefl`,
  `EqNatSound`) are pinned on their types.
- **R3/R4 depend on the pin.** `nat_add::register` turns the rules on only
  if `holds(add, Builtin::Add)`.
- **`List.length`'s run body** (`elab/src/lib.rs:3044`) is unpinned, but it
  runs only at run time. `set_run_body` says it never unfolds in the kernel
  (`check.rs:1991-1997`), so it is SW-1991's concern, not soundness.
- **A stale `Float` still refuses in a fallback session.** SW-1991 already
  notes this, so it isn't a new finding.

## SW-1916: the `"""` pre-scan uses the lexer

### L1. A comment inside `${…}`: the message misleads (low, high, S)

`"""⏎  ${x -- }⏎  """` is refused with "a `${…}` in a `"""` text stays on
one line" (`lexer.rs:367`), and the span runs from `${` to the newline. The
user wrote it on one line. The real cause is that `--` runs to the end of
the line and takes the `}`. The main pass would say the same.
**Recommend:** in `interp` mode, when the newline is reached and the last
thing lexed was a comment, say "a comment in a `${…}` runs to the end of the
line, so it takes the `}`", with the comment as the label.

### L2. `invisible` misses some characters that show as nothing (low, medium, S)

The fallback arm `ch.is_whitespace() || ch.is_control()` (`lexer.rs:1294`)
catches the Cc controls and the Unicode spaces. It misses the Cf (format)
characters outside the table, and these show as nothing too:

- U+2061–U+2064 (FUNCTION APPLICATION, INVISIBLE TIMES, INVISIBLE SEPARATOR,
  INVISIBLE PLUS), which text pasted from mathematics tends to carry;
- U+180E (MONGOLIAN VOWEL SEPARATOR);
- U+034F (COMBINING GRAPHEME JOINER);
- U+061C (ARABIC LETTER MARK), a bidi mark that the bidi arm also misses;
- U+FFF9–U+FFFB;
- the tag characters U+E0001 and U+E0020–U+E007F.

Each of these is printed in backticks, so the message reads
"unexpected character ``" with nothing between the backticks. **Recommend:**
add these ranges, with "it shows as nothing: delete it", and put U+061C
with the direction controls. Add one case to
`invisible_characters_are_named`.

### L3. Bidi controls pass silently in comments and text (low, high, S–M; D2970)

The lexer now names U+202A–U+202E and U+2066–U+2069 where they are already
errors, in code. In a `--` comment, though, the lexer skips to the newline
without looking at the characters. In a text literal, `scan_string` and
`scan_block` keep them. This is the Trojan Source pattern (CVE-2021-42574):
a comment or string that shows one order of text while the compiler reads
another. It matters more in a proof language, where reading the statement
is the trust. Rust denies it by default
(`text_direction_codepoint_in_comment`, `…_in_literal`). It predates SW-1916
and isn't a regression. D2970 asks whether to warn.

### Tests

- The new tests check codes and messages, but no spans. The brief asked
  about positions. I read them as right: `lex_from` keeps absolute byte
  offsets, and every error is built from `i`, `dollar` or `start`, never
  from `line_start`. A test should still pin one span. For example, "stays
  on one line" should start at the `${`, and "isn't closed with `}`" should
  start at the `${` and end at the end of the file.
- No test runs the F1 repro through `lex_with_trivia`, the formatter's
  path (`keep_trivia = true`). The pre-scan always lexes without trivia,
  and I found no way for trivia to change where a token ends. A one-line
  test would keep it that way.

### Comments

The test comment at `lexer.rs:1813` ("the `"""` pre-scan once ended a
`${…}` by its own rules … and the lexer then sliced the text backwards and
panicked") is history. "A `}` inside a literal in a `${…}` doesn't end it,
and the pieces line up with the main pass" says what the test guards. The
code comments are fine: they say why, as at `lexer.rs:940`, "found by the
lexer itself, so that a `}` in a nested literal is read the same way here
as in the main pass".

### Checked and sound

- **The two passes agree on where a `${…}` ends.** `lex_from` in `interp`
  mode runs the same loop over the same bytes. The state it starts from
  (`fresh_line = true`, empty `tokens`) changes only trivia and `--|` bars,
  never where a token ends. Whether `'` starts a character is decided
  inside the name and number loops (`x'` is a name), not from the previous
  token, so it is the same in both passes.
- **Nesting is bounded.** A `"""` inside a `${…}` is refused in `interp`
  mode at any depth (`lexer.rs:521`), so `scan_block` doesn't recurse.
  Ordinary strings nested inside go through `scan_string` and the `interps`
  stack, as in the main pass. Record braces `${ {a = 1}.a }` are tracked by
  the bottom entry's `depth`.
- **The cost stays linear.** Each `${…}` is lexed twice in all, once by the
  pre-scan and once by the main pass, and each `"""` is pre-scanned once.
  No input re-lexes a text quadratically.
- **The guards that remain can't fire, and don't panic if they do.** The
  `piece.from == text_start` check (`lexer.rs:650`) and pass 2's
  `dollar == j` check (`lexer.rs:995`) return E-PARSE "a compiler bug"
  instead of slicing. Pass 1 and pass 2 skip `\$` the same way.
- **The unclosed cases at the end of the file are errors.** These are
  `${x` and `${"${x`, which the tests cover.

## SW-1820: language server panic recovery, stage 1

### S1. The search-panic test stops short (medium, high, S)

`Faults::search_panics_now` panics "before they start" (`lib.rs:736`),
inside the `catch_unwind` but before `search.run`. So the test
`a_panicking_search_is_answered_and_the_next_search_works` never has a
session in use, `WARM` taken out, or thread-locals such as `NO_ETA` set.
Those are what a real panic leaves behind, and they are why the worker is
replaced rather than reused. A regression that reused the thread, such as
dropping the `return true` in `search_worker`, would still pass. A
regression in the restart itself shows as `recv_timeout(120 s)` ("the
server went quiet"), not as an assertion. The test also doesn't check
`searches.running` (through `search_peak`), which the design (§3.2) said
must come back down.

**Recommend:** move the fault point inside `with_project_session`'s `f`.
Make it count searches, so the test can assert that the second search ran
on a new thread: count `WARM` constructions, or record the thread's id in
a test hook. Use a short timeout with a message. Assert
`search_peak == 1` after two searches.

### S2. `Main::request`'s safety argument is wrong (low, high, S)

The comment at `lib.rs:821` says: "the handlers read the server's state
without changing it, so the main thread is still sound". `code_action`,
`context_at` and `member_completion` call `queue_search`. That calls
`supersede`, which cancels and answers other pending searches, and inserts
the new search into `searches.pending`. The real invariant is weaker but
holds. Each change is one locked map operation, and answers go through
`PendingSearch::answer`'s exactly-once swap, so a panic between two of
these steps leaves a consistent state.

With one exception. `queue_search` inserts into `pending` (`lib.rs:1111`)
*before* it evaluates `make(version)` (`:1116`). A panic in `make` leaves
an entry, and no job is ever queued for it. The catch then reads the entry
as "a search already queued is answered by its worker" and sends nothing.
The request hangs until a later request of the same kind, or an edit,
supersedes it. Today's `make` closures only move values, so this can't
happen yet. **Recommend:** build the `SearchJob` first, then insert and
send. Restate the comment as the real invariant.

### S3. The catch covers only `search.run` (low, high, S)

A panic elsewhere in `run_search` unwinds out of the worker. That covers
the `search_delay` loop, `searched` (which locks and serializes), and
anything in `Search::run`'s callers outside the closure. The supervisor
sees `Err` and restarts the worker, but that job's request is never
answered and `searches.running` stays incremented. Nothing reads `running`
except the peak, so the cost is the unanswered request until it is
superseded. **Recommend:** put the whole body after the cancel check under
one `catch_unwind`, with the `fetch_sub` and the null answer in the
handler, or behind a drop guard.

### S4. Docs that are wrong about the playground and `Faults` (low, high, S)

- `run_search`'s doc says that when it returns false, "the caller must drop
  everything the thread owned". `Inline::tick` (`lib.rs:2831`) ignores the
  value. In the browser that's moot. `wasm32-unknown-unknown` aborts on a
  panic, so `catch_unwind` in `run_search` and in `Main::request` does
  nothing there, and the page's worker restart is the recovery
  (`lsp-failure-policy.md` §6). Natively, `Inline` is used only by tests.
  The SW-1820 ticket's "Playground path catches but doesn't restart" is
  wrong: in the playground nothing catches. Say so in `Inline`'s doc, and
  have `tick` say why it ignores the flag.
- `Faults`' doc says "A relaxed load per search or request when nothing is
  set". A request takes a `Mutex` lock (`request_panics_now`), and a search
  does a `SeqCst` `try_update`. Both are negligible, but the sentence is
  wrong. Say "a cheap check".
- The test doc at `faults.rs:113` ("SW-1820, SW-1808 finding 3: the search
  worker's panic left the request unanswered and ended the only worker")
  is history. Say what it guards: "a search that panics is answered with
  null, and the next search works".

### Already filed, not repeated here

- The restart budget is SW-2067, and the playground's budget SW-1981.
- Cancelling pending searches at shutdown, and wiring cancellation into
  project searches, is SW-2066.
- The per-candidate catch in `search.rs:1402` and the `NO_ETA` guard are
  SW-1979.

The first-internal-error notice (D2742, §3.5) isn't in this merge. The
policy note's stage list puts "the notices" in stage 3 (SW-1948), so this
isn't a gap in stage 1.

### Checked and sound

- **No double responses.** The direct path sends only after `answer`
  returns. The search paths answer through `PendingSearch::answer`'s swap.
  The catch sends its error only if `pending` has no entry for the id, and
  no code runs after a successful `queue_search`. So a handler can't panic
  once its search is queued.
- **Panics don't leave locks behind.** `lock()` recovers a poisoned mutex.
  `nav.read()` does too, and read guards don't poison anyway. `RefCell`
  borrows are released while the panic unwinds.
- **Shutdown is clean.** When `main` is dropped, so is the only
  `Sender<SearchJob>`. Each worker's `for job in jobs` then ends, the worker
  returns false, and its supervisor returns. `serve_from` joins the
  supervisors, which join their workers. A worker that panics while
  shutting down is restarted once, finds the channel closed and ends.
  Supervisors hold no job sender, so they can't keep the channel open.
- **If no worker can be started, requests are answered.** When
  `spawn` fails, the supervisor logs and returns. If it was the last one,
  its receiver is dropped, `to_searches.send` fails, and `queue_search`
  answers null. Jobs already queued at that moment are dropped. They are
  answered when superseded.
- **`WARM` is handled correctly.** A search takes it out while in use
  (`lib.rs:3117`), so after a panic nothing is left in the thread-local,
  and the new thread starts empty. On a normal exit it is dropped
  explicitly, before the thread-local destructors run (SW-1808 finding 8).
- **The cancellation comment.** The rewritten `PendingSearch::cancel` doc
  matches the code, and SW-2066 tracks the wiring.

## The 1 Nov review's findings in scope

From `docs/research/rust-codebase-review.md`:

- **§1.4, background proof actions with no version guard or bounded
  pool: fixed** (before these merges). Searches run on a bounded pool
  (`search_workers`). `searched` answers null unless the document is still
  at the version the search was computed from, and edits are versioned
  `documentChanges` when the client supports them.
- **§4.1, mode changes restored by hand, and a stated policy that a
  panicked session is discarded: partly done.** The search worker now
  throws its thread and kept session away after a panic, which is the
  policy. The main thread keeps its state on the read-mostly argument (S2
  above). The guards (`NO_ETA`, `cancellable_at`) and removing the
  per-candidate catch are still open (SW-1979).
- §4.2 and §4.3 (native ABI) are out of these merges' scope.

## Tickets to file

Grouped into lanes:

1. **Pins: one check at binding, and the comments** (Sonnet, 45 min).
   Folds into the start of SW-1991 if that lane is next, and otherwise
   stands alone. P1, P2, P3, P4: check every pinned builtin in
   `bind_builtin_def` and `bind_builtin_data`; give `pinned_hashes`'s
   session the fallback so it lists every stale pin; correct `pins.rs:21`;
   gate the fallback behind `test-bypass`; test two definitions for one
   native; a message for each refusal. Tests: `task test:one --
   pinned_hashes`, `a_native_is_registered_once`, the core glue test,
   `a_changed_native_definition_refuses_the_prelude`, and extract's
   `a_changed_*`.
2. **Language server stage 1 follow-ups** (Sonnet, 45 min). Runs before or
   with SW-2067, since both touch `keep_search_worker`. S1, S2, S3, S4: a
   fault point inside the search, with assertions on the restart and on
   `search_peak`; build the job before inserting it into `pending`; one
   catch over the whole job; correct the docs of `Main::request`, `Inline`,
   `Faults` and the test. Tests: `task test:one -- faults`, and the lsp
   search tests by name.
3. **Lexer messages for hidden characters** (DeepSeek, 30 min). L1, L2: a
   specific message for a comment inside `${…}`, the missing format
   characters, span assertions on two `${…}` errors, and the F1 repro
   through `lex_with_trivia`. Tests: `task test:one --
   text_block_interpolation`, `invisible_characters_are_named`.
4. **If D2970 is yes: warn on bidi controls in comments and text**
   (Sonnet, 45 min). A warning code in the lexer for U+202A–U+202E,
   U+2066–U+2069 and U+061C in comments and literals, with the guide and
   `docs/syntax.md` updated (a new user-visible warning). Tests: the
   lexer's unit tests and one `examples/` file.

## Questions for Matt

- **D2970:** bidi direction controls (U+202A–U+202E, U+2066–U+2069) in a
  comment or text literal are accepted silently today. They can make a
  statement or comment show differently from what the checker reads (Trojan
  Source). Should the lexer warn on them, as Rust does (deny by default),
  with an escape such as `\u{202E}` for a text that really needs one? [rec:
  yes, as a warning in comments and literals. Zero-width characters stay
  allowed in text, where they're sometimes meant.]

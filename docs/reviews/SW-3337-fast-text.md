# SW-3337 review: fast text (T1 of file-io-and-text.md)

Reviewer: Opus, 15 Nov 2026. Branch `lane/SW-3337` (bad2f6eec, 815d12f65 and
two board commits), read against `main` at e2b1cb075 and against
`lane/SW-3338` (Files). Read and reasoned; no tests run (the lane's runs are
listed on the ticket, and the differential tiers compare against the
reference evaluator, which runs the definitions, see §2).

**Verdict: merge after two small fixes** (1 and 2 below). Everything else
is a follow-up.

## Findings, ranked

### 1. Merging with SW-3338 won't compile (two lines). Must fix in whichever lane merges second

`git merge-tree lane/SW-3337 lane/SW-3338` merges with no textual conflict,
but two of SW-3338's new lines in `crates/rt/src/run.rs` pass
`prims::text_of(..)`, which is now `&Text` with no `Deref` to `str`, to
functions that take `&str`:

- `crate::host::print_error(output, crate::prims::text_of(&field()))?;`
  (SW-3338's run.rs:1114)
- `files::write(&host, crate::prims::text_of(&text))` (SW-3338's run.rs:1176)

**Fix:** `&crate::prims::text_of(..).to_str()` in both. SW-3338's other
text constructions (`Value::text(text.into())` from `String`,
`Value::text(name.into())`, `message.into()`) still compile, through
`From<String> for Text`, and `from(String)` takes an ASCII file's buffer
as it is, with no copy, as files.rs:72's comment hopes. The version bumps (codec 3→4,
linked 2→3) don't clash: this lane bumps neither, and both lanes append
to `wire.rs`'s tag lists without textual conflict. The prelude hash
snapshot merges cleanly too, but it should be regenerated after the merge.

### 2. `Text.repeat` silently returns a shorter text than its definition when the result passes 2^32 − 1 characters. Should fix before merging (two lines)

`crates/rt/src/prims.rs`, `TextRepeat`:
`let n = n.min(u32::MAX as usize / t.len().max(1));`. The old clamp
(`isize::MAX / len`) was unreachable, because memory ran out first. The
new one can be reached. The default work limit is 10^10 steps
(`core/src/budget.rs:170`), and `text_repeat_cost` charges `n × utf8_len`.
So `"a".repeat 5_000_000_000` is charged 5×10^9 steps, which is under the
limit, and then returns a text of 4,294,967,295 characters, where the
definition says 5,000,000,000. `"ab".repeat 3_000_000_000` is the same
case. A native whose result differs from its definition is exactly what
the pinning argument rules out. It needs about 4 GB, so it's unlikely in
practice, but the answer is wrong, and nothing reports it.

**Fix:** never truncate. Either have `text_repeat_cost` return `u64::MAX`
when `n × len > u32::MAX` (the program then runs out of steps, an honest
resource failure), or panic with the same internal error as
`Text::whole`. In the end, finding 3's clean error covers it.

### 3. The 2^32 − 1 limit is reachable from user code and fails as a Rust panic. Follow-up ticket

`text.rs:116`, `Text::whole`: `panic!("internal error: a text of {len}
characters, more than a text can hold")`. User code can reach it:

- `IO.readAll` on an input of more than 4 G characters (`run.rs`,
  `Text::from(read_all(..)?)`), and SW-3338's `Files.read` likewise;
- `++`, `Text.concat`, `joinWith` or `split`/`join` whose total passes the
  limit (`Text::join`), for example 32 doublings of a 1-character text,
  each of which costs one step.

It's an internal error, but the user did nothing wrong. Also, `join`
allocates and fills the whole buffer before `whole` checks the length, so
the failure comes after gigabytes of work. **Fix:** check the length
before allocating (in `join`, `repeat` and `From<String>`), and turn it
into a resource error the runners already report (in the style of "a text
of more than 4,294,967,295 characters, the most one can hold"). On the
machine and in native code that probably means a fallible native
(`charge_prim` already has a way to fail). Readers return a `RunError`.
The design (§4.2) accepted the cap; this ticket is only about how it fails.

### 4. `native_abi.rs` still documents byte 16 of a text as its length. Low, fix in passing

`native_abi.rs:109-110`, `LEN_AT`: "Where a slice's length is
(`Value::Data`'s cell, `Value::Text`)". The safety comment in `words`
(about line 140, "the length at bytes 16-23 for `Data` and `Text`") is
likewise stale. For a text, bytes 16-19 are now the start and bytes 20-23
the length, in characters. Today, no native code reads `LEN_AT` for a
text (the only user is the probe), so nothing is broken. But the next
native author who inlines `Text.length` would read `start | len << 32`
as the length. **Fix:** remove `Value::Text` from `LEN_AT`'s doc, and add
`TEXT_START_AT = 16`, `TEXT_LEN_AT = 20` beside it, which the probe
checks (it already checks `tw[2] == 1 | 3 << 32`).

### 5. Small doc and lemma points. Low

- **Copy rule wording.** `Slice.sw`'s module doc and the `syntax.md`
  "Cost when run" bullet say "a slice of at most 32 characters, from a
  text of 1,024 or more, is copied". The test is on the *buffer's* length
  (`self.units.len() >= COPY_FROM`), not the text's. A 10-character slice
  of a 100-character piece of a large file is copied. "from a text whose
  buffer has 1,024 or more" or "cut from a large text" would be accurate.
- **A doc comment is missing.** `Text.charListsOfMap` (Text.sw:100) is a
  public std theorem without a `--|` doc comment (D2351: std gets full API
  docs).
- **A hypothesis isn't needed.** `Text.lengthSlice` takes
  `ordered: from ≤ to`, which it doesn't need: when `to < from`,
  `to - from = 0` and the slice is empty. Dropping it gives a lemma that's
  easier to apply. It's optional, and it changes the hash, which is fine
  for a new lemma.
- Each lemma says what its name claims. I checked `sliceToList`,
  `lengthSlice`, `sliceAppend` (holds past the end too, rightly with no
  `within`), `sliceAll`, `getSlice` (`inside` is needed), `getOrGet`,
  `getLtGet`, `concatToList`, `List.takeAdd` and `joinTextCharsEmpty`.
  `Text.concat := Text.joinWith texts ""` matches §4.1.

### 6. Performance notes. Follow-ups, not defects

- **Two allocations a text.** `Rc<Units>`, where `Units` holds a
  `String` or `Vec`, means two heap allocations per new text and two
  pointer hops per `get`, where `Rc<str>` used one. It's the natural
  shape for T2's in-place `++`, since the inner buffer can grow, so it's
  defensible. But programs that make many small texts (`Nat.toText`,
  `split` into short fields that are copied) pay an extra allocation each.
  Worth a look at `bench:aoc`'s allocation counts after the merge (the
  lane didn't run the benchmark, within its budget).
- **`contains` on non-ASCII texts.** `TextContains` encodes both texts as
  UTF-8 (`to_str()`) on every call when either buffer isn't ASCII. It's
  O(n), as before, but it allocates per call, for example once per line in
  a loop over a non-ASCII file. When the widths match, a search on the
  unit slices would avoid it.
- **Spare capacity.** `From<String>` keeps the `String`'s spare capacity
  (`read_all`'s buffer can be up to 2× its length). A `shrink_to_fit` for
  large inputs is cheap.

## What I checked and found right

**Natives against their definitions** (the definitions are the spec):

- `get`, `getOr` and `getLt` past the end give `None`, the fallback, and an
  internal panic that the erased proof rules out, in that order. Argument
  order is (text, index, fallback), as in `Text.getOr`'s definition. IR
  arities are 2/3/2, with `getLt`'s proof erased, as `Array.getLt` does.
- `slice` past the end, backwards, or with a `BigNat` bound: `start =
  min(from, len)` and `end = start + min(to ∸ from, len − start)` is
  `(drop from).take (to ∸ from)` exactly. A `BigNat` maps to
  `usize::MAX`, which gives the definition's result in every combination.
- `take`/`drop` beyond the length return the whole text or `""`.
  `drop 0` and `take ≥ len` return the argument itself.
- `concat` is `join(.., None)`, `joinWith ""`. `trim` keeps the old
  `char::is_whitespace` predicate, and an all-space text gives `""`.
  `split` gives the same pieces as `str::split`, as before.
- Characters above U+FFFF go in four-byte buffers, and U+D7FF, U+E000,
  U+FFFE and U+FFFF in two-byte ones. `bmp_char` never meets a surrogate,
  since every unit was made from a `char`. The unit tests and differential
  alphabets include the ends of the surrogate gap and U+10FFFF.
- Widths at `++` and `concat`: `join` widens to the widest piece's actual
  width and narrows a wide buffer's ASCII piece (`width()` rescans only
  non-ASCII buffers).
- Equality and order are by content. Same-width pieces compare as unit
  slices, and each width's units are scalar values (no surrogates), so
  slice order is scalar order. Mixed widths compare by `chars()`. The fast
  path (same `Rc`, start and length) is sound. Nothing hashes a `Value`,
  so there is no hash to keep consistent.
- Raw bytes: `Units` is private, and `Text` has no `Deref`, so the compiler
  catches any reader that assumes UTF-8. The only byte-level readers are
  `ascii()` (one-byte buffers only), the fold's forwards table (built from
  an ASCII literal, `.ascii().expect`), and `linked.rs`, which writes
  `to_str()`.

**The checker:** unaffected. The kernel and core evaluator never see
`rt::Value`. `crates/core` gains only `Builtin` names (`Home::Library`),
which nothing in core evaluates. The prelude snapshot gains 15 names and
changes none. `Text.get`'s existing hash is the one now pinned. The
differential tiers' `reference()` is `Session::run_main`, the core
evaluator running the definitions, so tiers 1 and 2 do compare natives
with definitions, as §4.4 asks.

**Native ABI:** `Text` is `repr(C)` `{Rc, u32, u32}`, so a `Value` stays at
24 bytes with the `Rc` at byte 8. The probe checks the buffer address,
start, length and count. Native code moves, counts and drops texts as
three opaque words (`from_words`/`sw_drop_words`) and never looks inside.
`sw_text_last` now passes positions, not byte offsets, and n1 only feeds
its result back in.

**Wire format:** the five tags are appended with no `FORMAT_VERSION` bump.
That's safe: both readers of serialized programs, `codec::decode` (the
standalone machine executable) and `linked::decode` (AOT tables), refuse
bytes from any other `BUILD_HASH`, and `stitchwort build` refuses a stale
runtime library by `BUILD_MARKER`. The check cache doesn't store runtime
values or `PrimOp`s. Linked files store texts as UTF-8, which is
independent of the layout.

**Memory:** the copy rule (≤ 32 characters from a buffer of ≥ 1,024) is
bounded, so slicing stays O(1), and slices of slices test the buffer's
length, so a short piece of a shared piece is copied too. Reference
counting is plain `Rc`. The shared `EMPTY` buffer is never unique, which
T2's in-place `++` will need. `still_owned` now counts the buffer's
references, the same `Rc` native code counts.

**JS:** the new natives are filtered out (`in_js`), so `run --js` runs
their definitions, which use JS's existing `take`/`drop`/`joinWith`
natives. `text_native_js`'s `unreachable!` can't be reached after the
filter.

**Docs:** the guide (chapter 6 and its checked example), `syntax.md` and
the performance-log entry match the code, apart from finding 5's wording.
The perf log's "against the reference evaluator" is accurate.

## Findings worth tickets

- Finding 3: a clean error for texts over 2^32 − 1 characters (readers,
  `join`, `repeat`), checked before allocating.
- Finding 6: allocation counts on `bench:aoc` before and after T1, and
  whether `Units` should be one allocation once T2's growth is settled.
- Finding 6: `contains` searching unit slices without encoding when the
  widths match.

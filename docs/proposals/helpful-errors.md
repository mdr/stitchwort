# Helpful compiler errors

**Status:** design note, 16 November 2026 (SW-3539, for D3642). Paper lane:
no builds, no tests. Nothing here is built.

Claims are marked **[measured]** (run with the main checkout's release
binary, or counted over the reject snapshots in
`crates/cli/tests/running/snapshots/`, at `7339b0a63`), **[source]** (read
in this repo's code at that commit), **[checked]** (read today in the
outside source linked), **[cited]** (from a paper, via the link or via
`docs/research/agentic-proving.md`, which read it), or **[inferred]**.

## In plain words

**The problem.** Most of Stitchwort's errors are good: they point at the
code, say what was expected, and often say what to do (`::` gets "write
`[x, ..xs]`", `.lenght` gets "did you mean `length`?", a slow check says
"make the number a variable"). The bad ones are bad in the same few ways,
and they are the common ones:

- 175 of the 206 type mismatches in the reject examples have the headline
  "type mismatch" and nothing else **[measured]**. When the two types are
  long, the one thing that differs (a `35` against a `36`) is buried in
  two 300-character types, one of them printed unfolded.
- Compiler internals reach the reader: `?1`, "the implicit argument `add`
  of `sumCong`", `(match …)` "hidden functions", `Call (L (%next …))`.
  27 reject diagnostics print a `?N` **[measured]**.
- The same long teaching note is printed under every error that has it: a
  file with five termination errors prints the same two 200-character
  notes five times. 85 notes in the reject snapshots repeat a note already
  printed in the same file, and 78 diagnostics have four notes or more
  **[measured]**.
- Help is uneven: `xs.lenght` gets "did you mean", `cuont` (with `count`
  in scope) doesn't; `::` gets a hint for Haskell habits, `by rfl` and
  `record` don't **[measured]**.
- The fixes the compiler already knows (add an import, add the missing
  arms, a style fix) reach the editor as quick fixes, but not the command
  line or its JSON, which is where agents work **[source]**.

**The change.** A house style (§3) and twelve small lanes (§5). The first
three: a type mismatch leads with where the two types differ, in the form
the user wrote; unsolved implicits are named in the user's words instead of
`?N`; a generic note is printed once per run and kept behind
`stitchwort explain CODE`. For agents: the JSON diagnostics carry
machine-applicable fixes, and common habits from Lean and Haskell get a
one-line "in Stitchwort this is …".

**What it should do.** The five worst messages in the audit (§1.3) go from
about 1,000–2,800 characters to 300–600, each leading with the actual
mistake **[estimated from the rewrites]**. No reject diagnostic prints a
`?N` or an internal name, a check that keeps it so runs over the reject
snapshots, and an agent can apply the compiler's own fixes without
parsing prose. About 7–9 hours of agent time in all, most of it Sonnet and
DeepSeek **[estimated, §5]**.

## 1. Audit

### 1.1 What was looked at

- **Which errors are common.** Over `docs/reviews`, `docs/research` and
  `board/`, the most-mentioned codes are E-RESOURCE (276 mentions),
  E-TYPE-MISMATCH (91), E-REFL (87), E-INTERNAL (59), E-MATCH-MOTIVE (58),
  E-PARSE (50), E-CANNOT-INFER (44), E-TERMINATION (42), E-CASES (40),
  E-UNKNOWN-NAME (33) **[measured]**: `grep -rhoE 'E-[A-Z][A-Z0-9-]+'`.
  Mentions are not occurrences, but they say what lanes talk about. The
  reject examples, one per error kind, have E-TYPE-MISMATCH (177 files),
  E-PARSE (89), E-REFL (69), E-ATTRIBUTE (57), E-TERMINATION (44)
  **[measured]**.
- **The friction record.** `docs/research/agentic-proving.md` §5 sorted
  the lanes' AoC and roguelike notes: "goals and terms shown unfolded,
  desugared or with hidden parts" (13 items) and "message hid or misnamed
  the real problem" (22) are 35 of the recorded friction items, and "cost
  the most time per item" **[cited, that note's own count]**.
- **The samples.** 25 diagnostics: the snapshot of each of the common
  codes, the three weak spots in the brief, and a scratch file of the
  mistakes a newcomer or an agent from another language makes first
  (`a.sw`, `d.sw`, `e.sw` in the lane's scratchpad) **[measured]**.

Rubric, one point each: **W** says where; **E** says what was expected and
what was found (– where that doesn't apply); **U** in the user's terms
(their names, their syntax, folded types); **M** names the likely mistake;
**F** suggests a fix; **L** short enough to read at a glance (under about
600 characters, no line over 200); **K** no internals leak.

### 1.2 Scores

| # | Code | Case | W | E | U | M | F | L | K | Score |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | E-UNKNOWN-FIELD | `xs.lenght` | ✓ | – | ✓ | ✓ | ✓ | ✓ | ✓ | 6/6 |
| 2 | E-UNKNOWN-NAME | `List.lenght` | ✓ | – | ✓ | ✓ | ✓ | ✓ | ✓ | 6/6 |
| 3 | E-UNKNOWN-NAME | `List.sum` needs an import | ✓ | – | ✓ | ✓ | ✓ | ✓ | ✓ | 6/6 |
| 4 | E-UNKNOWN-NAME | `cuont`, with `count` in scope | ✓ | – | ✓ | ✗ | ✗ | ✓ | ✓ | 4/6 |
| 5 | E-UNKNOWN-NAME | `:= by rfl` (Lean habit) | ✓ | – | ✓ | ✗ | ✗ | ✓ | ✓ | 4/6 |
| 6 | E-PARSE | `record Point …` | ✓ | ✓ | ✓ | ✗ | ✗ | ✓ | ✓ | 5/7; also cascades to E-UNKNOWN-NAME `Point` |
| 7 | E-PARSE | `x :: rest` pattern | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7 (says "found `:`" for `::`) |
| 8 | E-PARSE | unclosed `(` | ½ | ✓ | ✓ | ✗ | ✗ | ✓ | ✓ | 4.5/7: points at the end, not the `(` |
| 9 | E-DEF-EQUALS | `let x = n + 1` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7 |
| 10 | E-TYPE-MISMATCH | `def g: Text := double 3` | ✓ | ✓ | ✓ | ✗ | ✗ | ✓ | ✓ | 5/7 |
| 11 | E-NOT-A-FUNCTION | `double 3 4` | ✓ | ½ | ✓ | ✗ | ✗ | ✓ | ✓ | 4.5/7: the mistake is one argument too many |
| 12 | E-NOT-A-FUNCTION | `twice start ()` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7 |
| 13 | E-NONEXHAUSTIVE | missing `Blue` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7, but `\| Blue => ?` prints above the box, and it says "alternative" where others say "arm" |
| 14 | E-TUPLE-PARTS | 4 parts for 3 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7 |
| 15 | E-REFL | `n + 0 = n + 1` | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 7/7 (the counterexample is the star) |
| 16 | E-REFL | `rfl-sides-alike-when-elided` | ✓ | ✓ | ✓ | ✓ | ✗ | ✗ | ✓ | 5/7: the difference is Note 2, after a 400-character Note 1; the label starts at column 324 |
| 17 | E-REFL | `match-helpers-print-alike` | ✓ | ✓ | ✗ | ½ | ✓ | ✗ | ✗ | 3.5/7: five notes, 2.8 KB, "hidden functions" |
| 18 | E-REFL | `refl-note-huge-parser-unfolding` | ✓ | ✓ | ✗ | ✗ | ✗ | ✗ | ✗ | 2/7: `%next`, `Call (L …)`, `Std.Effect.bind` |
| 19 | E-TYPE-MISMATCH | `parser-count-differs-from-lemma` | ✓ | ✓ | ✗ | ✗ | ✗ | ✗ | ½ | 2.5/7 |
| 20 | E-TYPE-MISMATCH | `implicit-interface-not-searched` | ✓ | ✓ | ✗ | ✓ | ✓ | ✗ | ✗ | 4/7: `[Std.Int.instAdd]` against `[?1 xs]` |
| 21 | E-TYPE-MISMATCH | `match-equation-leaves-solution` | ✓ | ✓ | ✗ | ½ | ✓ | ✗ | ✗ | 3.5/7: the `4` against `5` isn't mentioned; four errors repeat two notes |
| 22 | E-INSTANCE-UNKNOWN-TYPE | `Nil == Nil` | ✓ | ✓ | ✗ | ✓ | ✓ | ✓ | ✗ | 5/7: `DecEq ?0` |
| 23 | E-TERMINATION | `termination-wrapper-same-size` | ✓ | ✓ | ✓ | ✓ | ✓ | ✗ | ✓ | 6/7, but 5.3 KB: the same two notes five times |
| 24 | E-OMEGA | `n + 1 = 2 + n` | ✓ | ✓ | ✗ | ✓ | ½ | ✓ | ½ | 5/7: "an integer model of the arithmetic abstraction satisfies the facts and the goal's negation" |
| 25 | E-RESOURCE | `as-written-unconfirmed-slow-check` | ✓ | – | ✓ | ✓ | ✓ | ✓ | ✓ | 6/6: says it isn't a type error, names the definition and the fix |

Every score is **[measured]** from the output; the scoring is mine.

**Headline.** 11 of the 25 score full or nearly so, and they show the
house already knows how: the counterexample under E-REFL, the
"did you mean" on fields, the import note, the `::` hint, E-TUPLE-PARTS's
part list, E-RESOURCE's "this isn't a type error". The weak ones cluster
in three places: **type mismatches** (#10, 19, 20, 21: a bare headline,
long types, the difference not named), **internals** (#17, 18, 20, 21, 22:
`?N`, hidden functions, runtime names), and **length** (#16, 17, 21, 23:
generic notes, repeated). Errors from other languages' habits (#4, 5, 6,
11) are a fourth, smaller cluster that matters most for agents (§4).

Across all 1,125 reject diagnostics **[measured]**: median 461 characters,
90th percentile 845, longest 2,688; 203 have a line over 200 characters;
191 (17%) repeat the headline word for word as the label.

### 1.3 The worst five, with rewrites

The rewrites are what the house style (§3) asks for. They are hand-written
targets, not output; where the compiler doesn't have the information today,
the lane in §5 says so.

**1. `parser-count-differs-from-lemma` (E-TYPE-MISMATCH, 2.5/7).** Today:

```
[E-TYPE-MISMATCH] Error: type mismatch
    ╭─[ reject/parser-count-differs-from-lemma.sw:12:3 ]
 12 │   Parse.readsExactly 36 Parse.digit DigitWritten Parse.readsDigit
    │   ───────────────────────────────┬───────────────────────────────
    │                                  ╰───── expected `∀ (start: Parse.Mark Char) => Parse.Fits Char Parse.Invariant.any start.rest → Parse.ReadsAt start (arg => Parse.exactly 35 Parse.digit) (read values => Parse.Each DigitWritten read values ∧ values.length = 36)`, but this has type `Parse.ReadsIn Parse.Invariant.any (arg => Parse.exactly 36 Parse.digit) (read values => Parse.Each DigitWritten read values ∧ values.length = 36)`
    │ Note: `Parse.ReadsIn Parse.Invariant.any (arg => …) (read values => …)` is `∀ (start: Parse.Mark Char) => Parse.Fits Char { holds = items => Unit, kept = read rest h => Trivial } start.rest → ∀ (total: Nat) … → … ∧ … → … → …`
```

The statement says `Parse.Reads (() => Parse.exactly 35 …)`; the expected
type is printed unfolded, and the `35` against `36` is left for the reader
to find in 500 characters. Rewrite:

```
[E-TYPE-MISMATCH] Error: this proves it for `Parse.exactly 36`, but the statement has `Parse.exactly 35`
    ╭─[ reject/parser-count-differs-from-lemma.sw:12:3 ]
 12 │   Parse.readsExactly 36 Parse.digit DigitWritten Parse.readsDigit
    │                      ─┬
    │                       ╰── 36 here; the statement has 35
    │
    │ expected: Parse.Reads (() => Parse.exactly 35 Parse.digit) (read values => …)
    │    found: Parse.Reads (() => Parse.exactly 36 Parse.digit) (read values => …)
    │                                            ^^
```

The parts are the first-difference search E-REFL already has
(`check.rs:1021`, `first_difference_note`) **[source]**; today it runs for
a mismatch only when the two sides print alike or elided (`check.rs:1190`)
**[source]**. Pointing the label at the `36` needs the argument's span,
which the elaborator has for an explicit argument **[inferred]**.

**2. `refl-note-huge-parser-unfolding` (E-REFL, 2/7).** Today (cut):

```
[E-REFL] Error: `rfl` can't prove this
 13 │ theorem lem (b: Bool): choose b (() => Parse.exactly 3402…456 Parse.digit) = (() => Parse.exactly 35 Parse.digit) := rfl
    │                                                         ╰─── `choose b (arg => …)` and `arg => Parse.exactly 35 Parse.digit` aren't equal
    ├─[ std/Parse/Parse.sw:252:23 ]
252 │ ╭─▶ def Parse.satisfy (what: Text) (passes: t → Bool): {Parse t} t := match Parse.next passes with
    │ ╰──── this `match`
    │ Note 1: computing both sides gives `choose b (arg => Call (L (%next Parse.isDigit)) (y => Std.Effect.bind (Std.Effect.bind (match y with …) …`
    │ Note 2: the left side is stuck on `b`: it can't compute further until `b` is known; a `match` on `b` (or `cases b`) splits it
    │ Note 3: `rfl` proves `a = b` only when both sides compute to the same value
    │ Note 4: `(match …)` is a `match` written inside `Parse.satisfy`, … (480 characters)
```

The useful line is Note 2. Rewrite:

```
[E-REFL] Error: `rfl` can't prove this: the left side depends on `b`
 13 │ theorem lem (b: Bool): choose b (…) = (…) := rfl
    │                        ────┬───               ─┬─
    │                            │                   ╰── `rfl` needs both sides to compute to the same value
    │                            ╰── stuck here until `b` is known
    │
    │ try: `cases b` (or `match b with`) and prove each case
```

No library source excerpt, no computed form of an effectful parser (it
means nothing to the reader), and Note 4 goes to `explain`.

**3. `match-equation-leaves-solution` (E-TYPE-MISMATCH, 3.5/7; first of
four).** Today:

```
[E-TYPE-MISMATCH] Error: type mismatch
 13 │   match field: slot.field with
    │                ╰────── the `match`'s scrutinee, still in this type
 14 │     | None => lem slot
    │               ╰───── expected `Q None 3 4`, but this has type `Q slot.field (?0 slot field) 5`
    │ Note 1: `?0` is the implicit argument `n` of `lem`, which wasn't worked out from the other arguments or the expected type
    │ Note 2: a term written out inside a branch (an explicit argument, or a type you wrote) isn't refined by the `match`: … (300 characters)
```

Three things differ (`slot.field` against `None`, an unsolved `n`, `5`
against `4`) and only the first is explained; `5` against `4` is a real
mistake and isn't mentioned. Rewrite:

```
[E-TYPE-MISMATCH] Error: `lem slot` proves `Q … 5`, but this arm needs `Q None 3 4`
 14 │     | None => lem slot
    │               ────┬───
    │                   ╰── last argument: 5 here, 4 needed
    │
    │ expected: Q None       3   4
    │    found: Q slot.field _n  5      (_n: `lem`'s implicit `n`, not worked out)
    │
    │ Note: `slot.field` in the result isn't replaced by `None`: only the goal and the
    │ variables in scope are refined by the `match` (explain E-TYPE-MISMATCH, "match")
```

Aligned columns are the type diff of §3.3. The three later errors in the
file keep only their first lines and "(same note as above)".

**4. `match-helpers-print-alike` (E-REFL, 3.5/7).** Today 2.8 KB: five
notes, two of which explain "a function that source can't name" and
"different hidden functions". The fact the reader needs is that the two
`match`es differ (`acc` against `acc + 1`); the counterexample (Note 5)
already shows it. Rewrite:

```
[E-REFL] Error: `foo xs = bar xs` is false: `foo [None]` is 0, `bar [None]` is 1
 11 │ theorem same (xs: List (Option Nat)): foo xs = bar xs := rfl
  8 │ def foo … (acc o => match o with | Some x => acc + x | None => acc)
    │                                                       ─┬─
    │                                                        ╰── `None` gives `acc` here
  9 │ def bar … (acc o => match o with | Some x => acc + x | None => acc + 1)
    │                                                       ───┬───
    │                                                          ╰── and `acc + 1` here
```

Rule: when the counterexample search says the statement is false, that is
the headline, and the notes on why `rfl` failed are dropped (no proof will
fix a false statement). The "hidden function" explanation stays for the
case where the statement may be true, and goes to `explain`.

**5. `implicit-interface-not-searched` (E-TYPE-MISMATCH, 4/7).** Today:

```
[E-TYPE-MISMATCH] Error: type mismatch
 15 │ theorem use ∀ (xs: List Int): xs.sumBy idI = xs.sumBy idI2 := sumCong xs idI idI2 fnSame
    │                         ╰── expected `List.sumBy [Int] [Int] [Empty] [Total] [Std.Int.instAdd] xs idI = …`, but this has type `List.sumBy [Int] [Int] [Empty] [Total] [?1 xs] xs idI = …`
    │ Note 1: `?1` is the implicit argument `add` of `sumCong`, which wasn't worked out from the other arguments or the expected type. Its type is an interface, but a plain implicit parameter is never searched for an instance: declare it `[auto add: …]` to have the instance found, or give it with `[add := …]`
    │ Note 2: the two types differ only in arguments the compiler fills in, shown here in `[brackets]` …
```

Note 1 is right and is the whole message. Rewrite:

```
[E-TYPE-MISMATCH] Error: `sumCong`'s `add` isn't found: it's a plain implicit, so no instance is searched for
 15 │ … := sumCong xs idI idI2 fnSame
    │      ───┬───
    │         ╰── `add` is left unknown here; `+` on `Int` was needed
    │
    │ try: `sumCong [add := Std.Int.instAdd] xs idI idI2 fnSame`,
    │   or declare it `[auto add: Add a]` in `sumCong`
```

### 1.4 What the audit doesn't cover

Warnings (21 W- codes), goals (`?`), the E-INTERNAL backstop, and the
editor's rendering. `docs/proposals/syntax-error-recovery.md` covers what
happens after the first syntax error; this note covers the wording of each
error.

## 2. Survey

### 2.1 Elm

Checked: Czaplicki, *Compiler Errors for Humans*, 30 June 2015
(elm-lang.org/news/compiler-errors-for-humans) **[checked]**.

- "The error shows the code exactly as you wrote it", with line numbers,
  so the reader asks "does this look like that?" rather than mapping a
  pretty-printed term back to the source.
- "Every message has a useful hint", naming the argument and the part
  that is wrong ("missing a field named `age`"), not "these two types do
  not match", which is "exactly what went wrong for the compiler".
- Layout: "General context is *above* the code. It is very short … If not,
  more specific hints are *below* the code." Colour draws the eye to the
  problem and separates messages.
- `--report=json` for editors, from the same release.
- The error-message catalogue (github.com/evancz/error-message-catalog):
  programs that trigger each message, to find patterns and judge changes.
- "Generating such specific error messages required no significant changes
  to the type inference algorithm": an extra bit of information on each
  type constraint.

The post's own text has no first-person message (its examples are
images) **[checked]**; the first-person voice ("I was expecting …") is in
later Elm releases **[inferred from memory, not re-checked]**.

**Steal:** the headline in the user's terms, the source as written, hints
below the code, and the catalogue, which Stitchwort already has in
`examples/reject` and its snapshots (1,019 files) **[measured]**: what it
lacks is a check over it (§5, lane 10). The constraint-carries-its-origin
idea is the way to "5 here, 4 needed": each expected type knows which
argument or annotation it came from. **Don't steal:** the chatty voice
(§6, decision 1).

### 2.2 Rust

Checked: the rustc dev guide, *Errors and lints*
(rustc-dev-guide.rust-lang.org/diagnostics.html) and *JSON output*
(doc.rust-lang.org/rustc/json.html) **[checked]**.

- Style: messages "start with a lowercase letter and do not end with
  punctuation"; "Error messages should be succinct"; "The word 'illegal'
  is illegal." `help` is for "changes the user can possibly make to fix
  the problem".
- Error codes, each with a long explanation shown by `--explain`.
- Structured suggestions with an applicability level: `MachineApplicable`
  ("should be automatically applied"), `MaybeIncorrect`,
  `HasPlaceholders`, `Unspecified`; "Be conservative when choosing the
  level". `cargo fix` applies the machine-applicable ones.
- JSON (`--error-format=json`): one object per line with `code` and its
  `explanation`, `spans` with `suggested_replacement` and
  `suggestion_applicability`, `children`, and `rendered`, the text a human
  would have seen.

**Steal:** all four mechanisms. The applicability level is the part that
matters for agents: a fix that is certain can be applied blind; one that
may be wrong is a hint. `rendered` in the JSON means a tool can show the
human text without a second run. **Don't steal:** the dense `help:`/`note:`
stack on hard trait errors, which is Rust's own known weak spot
**[inferred]**.

### 2.3 Gleam

Checked: *Fault tolerant Gleam*, 27 May 2024
(gleam.run/news/fault-tolerant-gleam/) **[checked]**; the `Ok` hint below is
from search results quoting gleam.run's rename-variable post, not read in
full **[checked, lightly]**.

- Analysis "moves on to the next definition in the module, returning all
  of the errors", rather than stopping at the first.
- Hints as a line of their own: "Hint: Rename this module and try again",
  "Did you mean `type One`?" for a type imported as a value, and (later
  releases) "Did you mean to wrap this in an `Ok`?".

**Steal:** the `Did you mean` line for the confusions that are specific to
the language (type against value, a missing wrapper), not only for typos.
Stitchwort already continues past a failed declaration.

### 2.4 Roc

Checked: roc-lang.org/friendly **[checked]**: a program with compile-time
errors can still be run, and crashes if it reaches the faulty code; the
page says the feature is only partly done.

**Steal:** nothing for messages. Running past errors is a separate
question (the closest is `docs/proposals/tests-with-errors.md`).

### 2.5 Lean 4

Checked: the Lean reference, *Error explanations*
(lean-lang.org/doc/reference/latest/Error-Explanations/) **[checked]**:
named explanations with a `lean.` prefix (`lean.unknownIdentifier`,
`lean.synthInstanceFailed`, `lean.ctorResultingTypeMismatch`), each
marked with the version it arrived in, 4.22.0 to 4.26.0.

Also cited: in MiniF2F failures, three Lean messages cover over half:
"linarith failed" 22.6%, "unknown identifier" 16.3%, "unsolved goals"
13.6%, and how often each is repaired varies a lot (Compile to Compress,
arXiv 2604.18587) **[cited, agentic-proving.md C12]**. Goedel-Prover-V2
repairs with `extract_goal`, the failing goal as a standalone statement
**[cited, C11]**.

**Steal:** explanations named after the code, written as reference pages;
Stitchwort has `GoalData.lemma`, its `extract_goal`, already
(`diagnostic.rs`) **[source]**. **Don't steal:** Lean's default type
mismatch, which prints both full types one after the other, much as
Stitchwort does now **[inferred from experience; not re-checked today]**.

### 2.6 Agda (and Idris)

Checked: Agda's quick guide (agda.readthedocs.io, v2.6.0): `C-c C-,`
shows a hole's goal type and context, `C-c C-.` also the type of what's in
the hole; `C-u` before a command shows types without normalising, `C-u
C-u` fully normalised **[checked, via search results quoting the guide]**.
Idris: not checked today.

**Steal:** the choice of how far to compute, made by the reader.
Stitchwort shows the goal as written and "computes to" under it (D3522)
**[source]**; the same two forms should be the default for type mismatches
(as written first), with `--full-goals`-style flags for more.

### 2.7 TypeScript, Swift

Not surveyed: nothing in the brief's questions needs them beyond what Rust
and Elm cover.

## 3. A house style for Stitchwort messages

Most of this is what the good messages already do. Written down, a lane
fixing a message knows the target, and the check in §5 (lane 10) can test
some of it.

### 3.1 Voice and tone

- Plain English, present tense, no blame, no jokes. Lowercase start, no
  closing full stop on the headline and labels (Rust's rule, and today's
  practice).
- **Impersonal, as now** ("expected `Text`, but this has type `Nat`"), not
  Elm's "I" (decision 1 in §6). The compiler is a tool, not a character;
  "I" adds words and nothing an agent can use.
- Say "you" only in a fix: "write `[x, ..xs]`", not "you wrote".
- The user's vocabulary: "arm", not "alternative"; "the statement", "the
  proof"; never "metavariable", "motive", "scrutinee" in a headline
  (allowed in `explain`). Where the guide has a word, use the guide's word.

### 3.2 Structure

1. **Headline:** the mistake, specific, in one line under about 100
   characters. Not the category: "type mismatch", "`rfl` can't prove
   this", "universe mismatch" alone are the category. When the compiler
   knows more (the difference, the counterexample, the argument count),
   the headline says it.
2. **Code**, as written, with the primary label on the smallest span that
   is wrong (the `36`, not the call), and secondary labels for where the
   expectation came from (the statement, the parameter). A label doesn't
   repeat the headline (191 do today).
3. **Details:** at most two short lines: `expected:`/`found:` aligned,
   when types are involved.
4. **`try:`** the fix, when there is one, as code that can be pasted.
   One per error; a second only for a real alternative.
5. **Notes:** what is specific to this error. Generic teaching ("however
   the recursive calls are repeated, some argument must get smaller …")
   moves to `stitchwort explain CODE`, and the error says
   `(explain E-TERMINATION)` once per run.
6. **Order of truth:** when the counterexample search finds the statement
   false, that is the headline and replaces the proof-failure notes.

Length targets: a typical error under 600 characters (median is 461 now
**[measured]**), none over 1,500 without `--verbose`; no source line wider
than about 160 columns in the excerpt (cut around the span with `…`).

### 3.3 Types: how much to print

- **As written first.** Print a type in the form the user wrote or the
  declaration states (`Parse.Reads …`), never unfolded unless the
  unfolding is the point. Goals already do this with "computes to"
  (D3522) **[source]**; mismatches don't.
- **Elide the agreeing parts, show the difference.** When the two sides
  are long (over about 80 characters), print both with the common parts
  as `…` and the first difference kept, aligned in two rows
  (`expected:` / `found:`), with the differing part marked. This reuses
  `first_difference_note` **[source]**. The full types are in the JSON and
  behind `--full-types`.
- **No compiler names.** An unsolved implicit prints as `_n` with a
  footnote "`lem`'s implicit `n`, not worked out", not `?0 slot field`.
  An instance prints as `Int`'s `Add`, not `Std.Int.instAdd`. A compiled
  `match` prints as `match o with …`, and its owner is named in prose,
  not as a "hidden function". Runtime forms (`%next`, `Call`, `L`,
  `Std.Effect.bind`) are never shown; print the call that produced them.

### 3.4 Proof failures

- Show the **goal** as a goal: hypotheses that matter, then `⊢ target`,
  written form first. The tactic errors already do this in places (E-CASES
  prints "goal: …"); make it uniform: `goal:` block, then what was tried.
- Say **what was tried and which step failed**, in one line each:
  "`omega` can't prove `n + 1 = 2 + n`: it's false at `n = 0`", not "an
  integer model of the arithmetic abstraction satisfies the facts and the
  goal's negation".
- For a unification failure inside a proof term, name **the argument**
  whose type didn't fit, and the two subterms that differ (rewrite 3).
- A statement found false outranks everything else (rewrite 4).

### 3.5 Colour

- Colour only on a terminal (today: `stderr().is_terminal()`,
  `main.rs:5078`) **[source]**, and also honour `NO_COLOR` (not read
  today **[source: no match in `crates/`]**) and a `--color=always|never`
  flag.
- Colour is redundant: nothing is said by colour alone, so the piped and
  snapshot form (no colour) carries the same information. The `^^` under
  a difference in §3.3 is there for the same reason.

## 4. Agents

### 4.1 What the evidence says

- **The message is what makes repair work.** Baldur's repair model only
  beat resampling when given the error message; removing compiler feedback
  "significantly lowers" Goedel-Prover-V2's self-correction; repair rates
  differ by message kind **[cited, agentic-proving.md C10–C12]**.
  RustAssistant, an LLM loop over rustc's errors, fixed about 74% of
  real-world compilation errors (Deligiannis et al., arXiv 2308.05177)
  **[checked: the abstract]**. LLMs can also rewrite poor messages into
  clearer ones for novices (Leinonen et al., SIGCSE 2023, arXiv
  2210.11630) **[checked: the abstract]**, which says the gap is in the
  message, not the reader.
- **In this repo:** 35 recorded friction items are messages that hid the
  problem or showed unfolded or hidden parts, the most time per item
  (agentic-proving.md §5) **[cited]**. A roguelike lane got 30 KB for six
  goals and grepped for the `⊢` lines; that led to `GOAL_LINE_LIMIT`
  (`render.rs`) **[source]**. SW-2836's review: a `cases` message split
  the wrong thing, and "the reader may think the statement is false"
  **[source: docs/reviews/SW-2836-sf-lists.md]**. SW-3344's: "the user
  never wrote `x` here" **[source]**. About 190 done tickets with
  "message", "note" or "diagnostic" in the title, 90 in the backlog
  **[measured: board titles]**: the messages are fixed one report at a
  time.
- **Agents use the CLI, not the language server** (agentic-proving.md §6)
  **[cited]**. The LSP offers quick fixes (add an import, add the missing
  arms, style fixes, goal fills; `lsp/src/lib.rs:1416–1720`) **[source]**;
  none of them is in `check`'s text or in `check --index`'s JSON, which
  has code, message, ranges, labels, notes, and for some codes `goal`,
  `counterexample` and `missing` (`driver/src/nav.rs:307–360`)
  **[source]**. The suggested import is in `Detail.import` but not in the
  JSON **[source]**.

### 4.2 What differs, and what doesn't

**The same as for humans** **[inferred]**: the headline that names the
mistake, the difference not buried, no internals. An agent misled by a
`?3` or an unfolded type spends a cycle exactly as a person does, and at
scale the cycles add up: every lane is a reader.

**Different:**

1. **Length costs context, not just patience.** A 5 KB error repeated
   over a loop fills an agent's window with five copies of the same
   notes. Generic notes once per run, behind `explain`, matter more for an
   agent than for a person who skims.
2. **Priors from other languages.** Agents write Lean and Haskell by
   habit: `by rfl`, `by simp`, `record`, `fun x =>`, `::`, `theorem … :=
   by`. Measured today: `::` is recognised, `by` and `record` aren't
   (§1.2 #5, #6). A short table of foreign forms, each with "in
   Stitchwort this is …", pays back most for agents.
3. **Fixes as data.** An agent can apply a `MachineApplicable` edit
   without reading prose, and should treat `MaybeIncorrect` as a hint.
   Today "did you mean `length`?" is prose in a note, so an agent must
   parse it.
4. **A stable code, and `explain CODE`.** The codes are stable already
   (tests match on them, `diagnostic.rs`) **[source]**; wording needn't be
   frozen, since agents read meaning, not exact strings. `stitchwort
   explain E-TERMINATION` gives the long form on demand, so inline text
   can be short. Lean's error explanations are the same idea **[checked]**.
5. **"try:" lines must be right.** A person weighs a hint; an agent tends
   to follow it. A wrong hint costs a cycle, and the SW-2836 case shows a
   misleading one can send a reader off course. So: only give `try:` when
   the compiler is confident, and say "maybe" otherwise
   (Rust's applicability, §2.2).
6. **The first error matters most.** Baldur trained repair on "the first
   occurring error" **[cited, C10]**. A cascade (`record` → unknown
   `Point`) costs an agent more than a person, who sees it is a cascade.
   Errors caused by an earlier error in the same run should say so or be
   dropped.
7. **Colour is noise to an agent**; it's already off when piped
   **[source]**.

## 5. Ranked improvements

Ranked by impact per effort. Estimates are agent time, scaled from past
lanes of a similar size (Opus and Sonnet run at about 0.3 of a
human-style estimate) **[estimated]**.

| Rank | Lane | Impact | Model | Est. |
|---|---|---|---|---|
| 1 | **Mismatches lead with the difference.** Run the first-difference search for every E-TYPE-MISMATCH whose sides are long, not only alike or elided; headline "… here, … expected" when it finds one; `expected:`/`found:` aligned rows with the agreeing parts as `…`; print the expected side as declared (folded). Rewrites 1 and 3. | high: 206 reject cases, the second-most-discussed code | Opus (printing beside the unifier; folding) | 1.5 h |
| 2 | **No `?N` in messages.** Print an unsolved implicit as `_name` with "`f`'s implicit `name`, not worked out" once; an instance by its interface and type. Rewrites 3, 5; #22. | high: 27 reject diagnostics, every unsolved-implicit error | Sonnet | 1 h |
| 3 | **A generic note once per run.** Mark generic notes as such at their sites; the renderer prints each once and later errors say "(see above)". The JSON keeps every note. | high for length: 85 repeats in the reject set; #23's 5.3 KB halves | Sonnet | 45 min |
| 4 | **Fixes in the JSON and in text.** A `fixes` list on `check --index` diagnostics: `{range, replacement, applicability}` from what the LSP already computes (import, missing arms, style) and the "did you mean"s; `try:` lines in text from the same data. | high for agents | Sonnet | 1.5 h |
| 5 | **Foreign habits.** A table in the parser and name lookup: `by …`, `record`, `fun`, `λ`, `->` where `=>` is meant, `where`, `deriving`, `simp`, `theorem … := by`; each "in Stitchwort this is …". | medium; high for agents | DeepSeek | 45 min |
| 6 | **Did you mean, everywhere.** Edit-distance suggestions (`stitchwort_elab::edit_distance` exists) for locals and unqualified names, as for fields. #4. | medium | DeepSeek | 30 min |
| 7 | **Too many arguments.** E-NOT-A-FUNCTION whose head is a known function says "`double` takes 1 argument, but is given 2", labelling the extra one. #11. | medium | DeepSeek | 30 min |
| 8 | **False first.** When the counterexample search says the statement is false, it is the headline and the why-`rfl`-failed notes are dropped. Rewrite 4. | medium | Sonnet | 45 min |
| 9 | **`stitchwort explain CODE`.** One page per code: the generic notes moved out of messages, the reject example and its output, the fix. Start with the 20 most common codes; the rest list their reject example. | medium; makes 3 and 8 possible without loss | Sonnet | 1.5 h |
| 10 | **A message check over the catalogue.** A test over the reject snapshots: no `?N`, no `%`, no `Std.Effect.`, no headline repeated as a label, no line over 200 characters, headline not just the category for the listed codes; a count that may only go down, as the audit counts do. | medium; keeps the rest | Sonnet | 45 min |
| 11 | **Small layout fixes.** Unclosed bracket: a second label on the opening `(`. E-NONEXHAUSTIVE's `\| Blue => ?` inside the box, and "arm" not "alternative". `::` says `::`. `NO_COLOR` and `--color`. Long source lines cut around the span. | low each | DeepSeek | 45 min |
| 12 | **Effectful terms folded in E-REFL.** Never print the runtime form of a parser or handler; print the call. Rewrite 2. Overlaps SW-794 (keep goals folded) and bounded readback. | medium, but the hard one | Opus | 2 h |

About 12 hours of lane time in the table, 7–9 likely at past ratios
**[estimated]**. Order: 1, 2, 3 first (in parallel; 1 and 2 both touch
type printing, so 2 after 1 if they clash); 4 and 9 together (both make
the compiler's knowledge available as data); 5, 6, 7, 11 as a DeepSeek
batch at any time; 10 once 1–3 are in, so its counts start low; 12 with
the bounded-readback work.

Prerequisite check for any rewording: `docs/proposals/error-kinds.md`
(SW-1908, done) moved path choices off message text; six
`message.contains`/`starts_with`/`ends_with` reads remain in
`crates/elab/src` **[measured: grep]**, and lane 1 should look at them
before changing mismatch headlines **[inferred]**.

What should improve, so we'd know: rerun this audit's 25 after lanes 1–3
and 8 (target: none under 5/7, median length down a quarter); lane 10's
counts; and the next friction synthesis's B + C count against today's 35.

## 6. Decisions for Matt

Numbers to be assigned by the orchestrator.

**Decision 1: the voice.** Elm made its errors speak in the first person
and conversationally ("I am looking for …", "Hint: …"). Stitchwort's are
impersonal and terse ("expected `Text`, but this has type `Nat`"). The
choice defines how the language sounds everywhere it talks to its users.
Options: (a) impersonal, plain, as now, with the structure of §3.2
(headline that names the mistake, code, `try:`); (b) Elm's first person.
**Recommendation: (a).** Elm's gains came from the content (the code as
written, the specific hint, the layout) **[checked: the post's own
reasons]**, not the pronoun; "I" lengthens every message and gives an
agent nothing.

**Decision 2: agent-facing errors as data.** Add `fixes` with an
applicability level to the JSON diagnostics, and a `stitchwort explain
CODE` command, and from then on treat a fix the LSP knows but the JSON
doesn't as a bug. Later, perhaps, `stitchwort fix` applying the certain
ones, like `cargo fix`. This is new user-visible surface (a command, a
JSON field); the cost is lanes 4 and 9, about 3 hours.
**Recommendation: yes** to the JSON fixes and `explain`; decide
`stitchwort fix` once agents have used the fixes for a while.

Not decisions (the orchestrator's): the house-style details, the length
targets, the order of the lanes, and which notes count as generic.

## 7. Tickets to file

One per row of §5's table, under the epic the orchestrator picks, each
linking this note; rank 11 can be one ticket. The audit's per-case
failures (#4, 5, 6, 8, 11, 13) are in those lanes, not separate tickets.

# Proposal: computing a value once (SW-2014)

Status: design note, waiting for Matt's decisions (D2880 to D2885). Absorbs SW-1576 and
SW-1602. Written 7 Nov 2026 from the friction synthesis, theme L
(`docs/research/aoc-friction-synthesis.md:340`).

## 0. Summary

**What users get.** A record can carry a value worked out from its fields, such as a
lookup table, written once in the type: `computed table: Map Nat Rule := ruleTable
numbered`. Every `rules.table` after that is a read, not a rebuild. In 2020 day 19 that
is the difference between 6.5 s and more than two minutes, and it removes the extra
"pass the table in" functions the day has now. Proofs see an ordinary definition, so
`rfl` and unfolding work as they do today.

**The problem, plainly.** You give a record a method that works something out from a
field, say a `Map` built from a list, and call that method in a loop. It looks like a
property of the record. It's actually a function call, so the map is built again on every
call. Nothing warns you; you find out from the timing. Six AoC days hit this. Two are
fixed, one is a different problem (§1), and three are still open.

**The recommendation.** Computed fields on records (design B, §3.2): a field declared in
the type with `computed` and a definition from the other fields. The kernel sees a
plain definition, `Rules.table rules = ruleTable rules.numbered`. The runtimes keep its
value in a hidden slot, filled when the record is built. Second, as a separate and
smaller stage: hoist small invariant values (numbers, booleans, characters) out of
lambdas automatically (C-narrow, §3.3), which fixes the other two open days without
the user doing anything. Also: a guide section, and a profiler line that names a
function called many times on the same value (§3.1), so people can find these cases.
Design D, a cache keyed on the identity of the value it's called with, is ruled out
(§3.4).

## 1. The six days

| Day | What was recomputed | Cost | State |
| --- | --- | --- | --- |
| 2020 day 19 | `rules.rule n := rules.table.get n`, with `Rules.table` a `Map.fromList` of a field | 6.5 s became more than 2 min | **Open.** Worked round by building the table once and passing `table.get` in (`aoc/src/Aoc/Year2020/Day19/Day19.sw:40`, `:165` to `:172`; notes `aoc/NOTES-2020.md:5351`) |
| 2020 day 15 | `starting.numbers.length`, once a turn | about 4% of the run, 15 M `List.lengthOnto` calls (SW-1602) | **Open.** Worked round by `Starting.nextAfter` taking `count` (`Day15.sw:52`, `:68`) |
| 2021 day 15 | `cave.height` (a list's length) inside the `level` lambda | 31.7 s against 17.6 s | **Open.** Worked round by a `let` outside the lambda (`aoc/NOTES-2021.md:3676`) |
| 2024 day 20 | a `let` used in a `match` arm inside a lambda | 28.4 s against 2.6 s | **Fixed.** The lifted `match` helper takes the `let`'s value from its caller, through a run body (`aoc/NOTES-2024.md:6523`; `crates/elab/src/lift.rs:76`, `:1403`) |
| 2025 day 1 | a proof field computed at run time | 4.2 s for 50 lines | **Fixed.** `run` and `test` erase proofs (`docs/aoc-2025.md:902`; `crates/core/src/erase.rs`) |
| 2021 day 9 | a `Graph`'s `states` list, needed only for termination, built with each graph | 2.3 s of 3.0 s | **A different problem:** the field is stored and wanted only by proofs, so the fix is erasing data that only proofs use, not sharing it (`aoc/NOTES-2021.md:2141`). Out of scope here. |

The three open days are of two kinds:

1. **A derived value of a record, used across many calls** (2020 day 19, and 2020 day
   15 in part). The value depends only on the record, but it's needed inside a
   recursive function that receives the record, or a closure over it, millions of times.
   Hoisting inside one function body can't see that the calls share an argument.
2. **A loop-invariant expression inside a lambda** (2021 day 15, and 2020 day 15 once
   `Starting.next` is inlined into the `Nat.iterate` lambda). The lambda reads a field and
   works something out from it on every call, though the answer is the same each time.

## 2. What the runtimes do today

All of this is read from the code. Where I inferred something, I say so.

- **A `let` is computed once, where it's written.** The machine is strict. A `let` is a
  register, filled once (`crates/rt/src/machine.rs:5-23`). So `let height := cave.height`
  outside a lambda shares the value with every call, and the same `let` inside the lambda
  computes it on every call. That's the semantics, not a bug.
- **A top-level constant is computed when first used, then kept** (`machine.rs:21`,
  `Ret::Const`). These are Haskell's CAFs.
- **A method call is a call.** `rules.table` is `Rules.table rules`. Nothing remembers
  the result.
- **The optimiser has no CSE and no let floating.** `crates/rt/src/opt.rs:1-35` lists
  its rules: inlining small non-recursive functions (arguments bound by `let`s, so no work
  is duplicated), beta, known constructors, case of case, known calls, copies of
  recursive functions for known function arguments. Nothing moves an expression out of a
  lambda. It says (`opt.rs:29-31`) that everything is pure and total, so work may be
  duplicated across branches without changing what a program prints. That is what makes
  hoisting sound here too.
- **One hoist exists, and it is deliberately narrow.** `crates/rt/src/hoist.rs:1-19`
  builds each closed `SigMap` once, in both backends. Its comment gives the rule this
  note keeps: only small values are hoisted, "since hoisting an arbitrary closed term (a
  long `List.range`, say) would keep its value alive for the whole run".
- **A definition can already run a different body from the one the kernel sees.**
  `Def::run_body` (`crates/core/src/globals.rs:106-114`, set by
  `crates/core/src/check.rs:1998`) is checked against the definition's type, never
  unfolded by the kernel, and not hashed. The runtimes lower it instead of the body:
  machine and native through `crates/rt/src/lower.rs:567` and `:909`, JS through
  `crates/js/src/lib.rs:2682`. It is used today for `decreasing` (the recursion without its
  fuel), for lifted `match`es (the 2024 day 20 fix), and in std (`List.length` runs as
  `List.lengthOnto xs 0`, `crates/core/src/registry.rs:359`). This is Stitchwort's
  `@[implemented_by]`, used only by the compiler, never written by users.
- **Native code compiles the machine's bytecode** (`crates/native/src/lib.rs:1-12`), so
  whatever lowering does, native gets. JS lowers from core terms separately, but shares
  erasure, `specialise.rs` and `hoist.rs` with the machine (`crates/js/src/lib.rs:25-31`).
- **Field defaults already compute a field from earlier fields**
  (`docs/syntax.md:481-517`; `FieldDefault`, `crates/core/src/globals.rs:324`: a
  generated helper and the fields it captures). But a default is "how a value is built,
  not a computed property". An update `{ r | numbered = … }` keeps the old value, and a
  literal can give the field a different value. So proofs can't rely on `table` agreeing
  with `numbered`, and a default can't be the fix.
- **A one-field record is stored as its field** (`docs/guide/11-running-and-shipping.md`,
  Performance notes). `Rules` is unboxed today. A computed slot would box it. That costs
  little, but it's a change.

## 3. The designs

Each design has the same four questions to answer:

- **Proofs.** What does the kernel see? The rule: always the plain definition.
- **Steps and determinism.** Can the same program, input and backend take different
  numbers of steps from one run to the next? Can a limit change an answer? (D2543:
  limits fail, they never choose.)
- **Memory.** What does it keep alive, and for how long? Does it make a value shared
  that was unique, so that in-place updates turn into copies (`docs/proposals/arrays.md`
  §6.1, the cliff)?
- **Which open days it fixes.**

### 3.1 A. Leave it to the user: a guide section, a lint, a profiler hint

**Problem.** People don't know a method call is a call. **Change.** A guide section,
"Keeping a derived value", that shows the slow method and the two fixes: a `let` outside
the loop, and a field filled by a constructor function. Add one of these two detectors:

- **A static lint** (SW-1576's idea): flag `Map.fromList`/`Set.fromList` of a parameter's
  field in a function that a recursive function calls. Cheap to write, but it guesses. It
  misses `cave.height` (a `length`, not a `fromList`), and it fires on code that is
  called only once.
- **A profiler line**, which I prefer: under `stitchwort run --profile`
  (`crates/rt/src/profile.rs`), count for each one-argument-dominant function how many
  *distinct* values its first runtime argument took, by pointer, and report `Rules.table:
  4.3 M calls on 2 values; compute it once (guide §…)`. It can't be wrong about what
  happened in the run, it costs nothing outside `--profile`, and it covers both kinds of
  case. Pointer identity is fine in a diagnostic, because nothing depends on it.

**Proofs:** nothing changes. **Steps, memory:** nothing changes. **Fixes:** none by
itself. It helps people find each case, and the workarounds keep two versions of a
function (day 19's `matchesCompletely` and `matchesCompletelyIn`), which is the clutter
we want to get rid of.

This is worth doing whatever else we choose: the guide section and the profiler hint go
with B and C below, as their stage 0.

### 3.2 B. A computed field, declared on the record

**Problem.** Day 19's table belongs to the rules: it's a fact about them, like their
count. **Change.** Declare it with the fields:

```stitchwort
type Rules = {
  numbered: List (Nat, Rule),
  --| The rules by number. Entries earlier in the list win.
  computed table: Map Nat Rule := ruleTable numbered
}
```

- **What the kernel sees.** `Rules` keeps one field. The declaration also makes a plain
  definition, `def Rules.table (rules: Rules): Map Nat Rule := ruleTable rules.numbered`.
  `rules.table` elaborates to a call of it, as a method does today. `rfl`, `unfold` and
  `rewrite` treat it like any definition. A literal can't give `table` and a pattern
  doesn't name it (`E-RECORD-FIELD` and `E-UNKNOWN-FIELD`, as for a field that doesn't
  exist). An update `{ rules | numbered = xs }` is a new `Rules`, so its table follows
  `xs`: the field can never be stale, by construction. That's the difference from a
  default.
- **What runs.** The runtime layout of `Rules` gets one hidden slot after its fields.
  Every place a `Rules` is built fills the slot by running the definition: the
  constructor, literals, updates, the constructor used as a function, and the JS decoder
  at an export (as it runs field defaults today, `docs/syntax.md:518`). `Rules.table r`
  lowers to a read of the slot, through a compiler-made run body on `Rules.table`
  (`check.rs:1998`). That run body is a projection. It's checked to have the right
  type, and its agreement with the plain definition rests on the lowering always filling
  the slot (§6).
- **When it's computed: at construction (eager).** Lean's `computed_fields` do the same.
  Values stay immutable: `Value::Data(tag, Fields)` (`crates/rt/src/value.rs:48`) gets one
  more field, with no new value form, no mutable cell and no thunk, in three runtimes.
  The cost: a computed field nobody reads is still computed every time a record is built.
  That's the trap of 2021 day 9's `states`, so the guide says it in one line ("computed
  when the record is built"). Laziness is D2882.
- **Updates that don't touch its inputs keep it.** The generated helper records which
  fields it reads, as `FieldDefault::captures` does (`globals.rs:325`). So `{ game |
  turn = t }` copies the slot instead of recomputing it when the computed field doesn't
  read `turn`. Without this, a computed field on a record updated in a hot loop would be
  recomputed on every update. That is the original problem moved to a different place.

**Proofs.** Unchanged in strength: theorems are about `Rules.table`, the plain
definition. Nothing new is trusted in the kernel.

**Steps and determinism.** The work moves from each call to each construction. That's
fixed by the program text, so it's the same on every run and differs only between
backends, as steps already do. No limit picks an answer. `run --reference` ignores the
slot and runs the plain definition (the reference evaluator lowers no run bodies,
which I inferred and haven't checked). That makes it the differential oracle for the
feature.

**Memory.** One slot per record, alive exactly as long as the record. Nothing is kept
beyond the record's life, so there's no leak of the CAF or full-laziness kind. One
hazard: a computed field that *is* (part of) another field, such as `computed grid :=
cells`, holds a second reference to it. Then an in-place `set` on that field copies
(arrays.md §6.1). The guide says so, and the copy note that names the site (D2590)
points at it.

**Fixes.** 2020 day 19 directly. 2020 day 15 (`computed count: Nat := numbers.length`)
and 2021 day 15 (`computed height: Nat := rows.length`), if the user declares them. So:
every open case, but the user has to opt in each time.

**Also rules out.** A computed field can't read itself, a later computed field, or a
method of its own type (that's the same cycle rule as field defaults,
`docs/syntax.md:517`). In stage 1 it's for records only (one constructor). Data types
with several constructors, and recursive ones (Lean's use: a hash cached at every node,
built from the children's), come later if a day needs them.

### 3.3 C. Hoisting loop-invariant expressions out of lambdas

**Problem.** In `cave.tiles`, `position.row % cave.height` sits inside a lambda that
runs once per position. `cave.height` is the same each time. **Change.** The compiler
moves an expression that reads nothing bound inside the lambda out to where the lambda
is made, and the lambda captures the value. This is GHC's full laziness, applied in a
strict language.

**The general version** hoists any invariant expression. It has three problems:

- **Memory.** A hoisted `List.range n`, or any big intermediate, lives as long as the
  closure, where before each call's copy became garbage at once. `hoist.rs:15-19` refused
  this for the same reason, and GHC's full laziness has the same known leak.
- **Sharing.** A value that was fresh in each call becomes shared by all calls. If the
  body updates it in place (an `Array.set`, list cell reuse), every call now copies.
  This is the arrays cliff, made by the compiler and invisible in the source.
- **Speculation.** An expression under a branch the lambda rarely takes would now run
  every time the lambda is *made*.

**C-narrow** keeps only the safe part. Hoist an expression out of a lambda when:

1. it reads no variable bound inside the lambda,
2. it is evaluated on every call (not under a branch or a `match` arm), so the work goes
   from "once per call" to "once per closure", and is worse only for a closure that's
   never called, by one call's worth,
3. its type is a small immutable value: `Nat`, `Int`, `Bool`, `Char`, `Float`, or a data
   type whose constructors have no fields. Like `SigMap`s, such a value costs nothing to
   keep, and it can't be updated in place.
4. it is pure (no ability). That's already true of anything in a pure lambda.

This runs on the machine's IR after `opt.rs` has inlined (so 2020 day 15's
`starting.numbers.length` is visible inside the `Nat.iterate` lambda). JS needs the same
rule on core terms: either a shared pass next to `hoist.rs`, or a JS-side copy. I'd
write one shared pass over core terms, applied to run bodies before both backends lower
them, and accept that it sees only what's written, not what inlining exposes. That's an
implementation choice, and I've made it: a shared pass, so the backends agree.

**Proofs.** Nothing. It's a runtime transformation of erased code, and the kernel never
sees it.

**Steps and determinism.** Fewer steps, fixed by the program text, so it's
deterministic. The answer can't change.

**Memory.** By rule 3, a few words per closure.

**Fixes.** 2021 day 15 with no change to the source. 2020 day 15 on the machine and
native, through inlining (I'd check with a profile, since this is inferred from
`opt.rs`'s size limits, not run). **Not** 2020 day 19: the table is a `Map`, which rule 3
excludes, and the repeated call crosses a function boundary (the closure `rules.rule` is
made once per message, then called inside `leftAfterWith`'s recursion).

A variant would hoist out of a partial application: compile `rules.rule` (that is,
`Rules.rule rules`) as `let t := rules.table in n => t.get n`. That would build the
table once per message, not once per lookup. GHC doesn't float between the lambdas of
one definition, so as not to change its arity (from memory, not re-checked). It also
brings back the memory problem for big values. I'm not proposing it.

### 3.4 D. A cache keyed on the value's identity

**Change.** Mark `Rules.table` `@[memo]`. The runtime keeps a table from the address of
`rules` to the result. **Fixes** day 19 with no change to the type.

**Ruled out:**

- **Wrong answers.** In-place reuse (SW-1163, `code.rs`) puts a new value in a uniquely
  owned cell's memory. A cache keyed by address then returns the old value's table for
  the new one. Avoiding that means weak references and invalidation on reuse in three
  runtimes. JS's `WeakMap` takes only objects, and Stitchwort's `Nat`s there are
  `bigint`s.
- **Unpredictable cost.** Whether a call hits depends on sharing, which inlining,
  one-field unboxing and reuse all change. The same program would take different
  numbers of steps from one build to the next. It would still be deterministic within
  one build, but nobody could reason about it.
- **Memory.** The cache keeps every key and result alive, unless it's weak (above).
- Hashing the value's contents instead costs as much as the `List.lookup` it replaces.

## 4. Other systems

- **Lean 4.** `@[implemented_by f]` swaps a definition's compiled code, unchecked. That's
  our `run_body`, but users can write it, so it's trusted. `Thunk α` is a structure
  around `Unit → α` that the compiler memoises. The kernel sees the function. The closest
  match is **`computed_fields`**: declared on an `inductive` (`with @[computed_field] hash
  : Name → UInt64`). The kernel sees an ordinary function defined by recursion. The
  compiler stores the value in each constructor and fills it at construction. That's
  design B, eager. This is from memory of `Lean.Elab.ComputedFields`, not re-checked.
- **OCaml.** `lazy e` makes a `Lazy.t`, and `Lazy.force` computes it once and overwrites
  the block. A record field of type `t Lazy.t` gives B's lazy variant, by hand. The
  optimiser (flambda) does some let floating, but nothing the user can rely on.
- **Haskell (GHC).** Laziness shares any `let` or `where` binding once it's evaluated, so
  `where table = …` inside a definition is computed once per call of the outer function.
  CAFs are top-level thunks, kept while referenced, and are a well-known source of
  retained memory. Full laziness (`-ffull-laziness`, on at `-O`) floats expressions out of
  lambdas. It's a known source of space leaks (the `[1..n]` floated out of a loop), and
  people turn it off locally for that reason. It's design C, unrestricted.
- **Koka and Roc** (Perceus reuse): no automatic floating that I know of. Both lean on
  uniqueness, which unrestricted floating would break, as §3.3 says. Not re-checked.

What we learn from them: the two systems with proofs (Lean) put the "compute once"
promise on the *data type* and keep the kernel's view plain. The systems that float
automatically (GHC) pay for it in memory surprises. That's the split this note
recommends: B for derived data, C only where it can't surprise.

## 5. Recommendation, and day 19 under it

**Recommended: B, computed fields (eager, records, with the slot kept across updates
that don't touch its inputs), plus C-narrow as an independent later stage, and A's guide
section and profiler hint as stage 0.**

Why B over C as the main fix: C can't fix the worst case (day 19, more than 20×). Making
C strong enough to fix it (big values, across calls) brings back exactly the memory and
sharing problems that `hoist.rs` and the arrays note were written to avoid. B puts the
promise where the user can see it, in the type. It costs nothing in the kernel, and
Lean has shown it works with proofs. Why not only A: the workarounds double the API
(`matchesCompletely` and `matchesCompletelyIn`) and they're found only by timing.

Day 19 under B:

```stitchwort
type Rules = {
  numbered: List (Nat, Rule),
  --| The rules by number, for looking one up without going down the list.
  --| Entries earlier in the list win, so it agrees with [`Rules.rule`]
  --| (`Aoc.Year2020.Day19.Proofs.tableRule`).
  computed table: Map Nat Rule := ruleTable numbered
}

def Rules.matchesCompletely (rules: Rules) (message: Message): Bool :=
  leftAfterWith rules.table.get (rules.enough message) 0 message.letters |> .any .isEmpty

def Received.matchingCount (received: Received): Nat :=
  received.messages.count received.rules.matchesCompletely
```

`matchesCompletelyIn` and the `let table` in `matchingCount` go. The table is built
twice in the run: once when the input is parsed, and once for part 2's `withLoops`,
whose update changes `numbered`. `Rules.rule` stays the `List.lookup` the spec uses.
`tableRule` (`Proofs/Table.sw:20`) is restated as `rules.table.get number = rules.rule
number`, and it unfolds `Rules.table` to the same term it has now. So the one use in
`Proofs.sw:66` changes its first argument and nothing else (inferred; the lane would
check it). The user could even write the method that was first tried, `rules.rule n :=
rules.table.get n`, and it would be fast.

## 6. Costs, risks and what this rules out

- **A new kind of field.** `syntax.md`, the guide's records chapter, the formatter, the
  LSP's hover, and the JS boundary (stage 1 leaves computed fields out of the TypeScript
  shapes, since the decoder recomputes them and the encoder omits them; I've decided
  that myself).
- **A compiler invariant the runtimes trust.** "Every construction fills the slot" is
  enforced by lowering, not by the kernel. It's the same kind of trust as `run_body`
  today (`check.rs:1992-1997`: "the runtimes are untrusted"). Tests: every construction
  path (literal, update, constructor as a function, JS decode, a value built inside a
  handler or resumption), run with the feature on against `run --reference`.
- **Eager costs a computation nobody reads**, once per construction. The guide says so.
  Laziness is D2882.
- **Unboxing.** A one-field record with a computed field is boxed (two runtime fields).
- **Hashes.** `Rules.table` is a new definition with its own hash. Whether the computed
  field is part of the type's hash is D2884: I'd say no, as for defaults
  (`docs/syntax.md:515`), but the runtime layout depends on it, so the image cache key
  must include it. Hash churn from the change isn't a cost (Matt's rule).
- **Rules out**, for now: users writing `implemented_by` (a second, unchecked body is a
  trust hole); memoisation by identity (D); unrestricted floating (general C).

## 7. Questions for Matt

- **D2880: Is computed fields on records (B) the language's answer to "compute this
  once", with the kernel seeing a plain definition?** [rec: yes. It fixes every open case,
  including the 20× one, adds nothing to the kernel, and follows Lean's
  `computed_fields`.]
- **D2881: Syntax: a `computed` field inside the type's braces (`computed table: Map Nat
  Rule := ruleTable numbered`), rather than an attribute on a separate `def`
  (`@[stored] def Rules.table …`)?** [rec: in the braces. It's found where the fields
  are, it reads like a field default with one word more, and it shares defaults'
  machinery (`FieldDefault`, the cycle rule). The attribute form would let a type's
  layout depend on definitions anywhere in its module.]
- **D2882: Eager (computed when the record is built) rather than lazy (on first read)?**
  [rec: eager for now. It needs no new value form or mutable cell in three runtimes,
  keeps values immutable for in-place reuse, and matches Lean. Add `lazy` later only if a
  day shows a computed field that's often built and rarely read.]
- **D2883: Also hoist small invariant values out of lambdas automatically (C-narrow:
  numbers, booleans, characters and field-less enums, evaluated on every call, pure)?**
  [rec: yes, as a separate stage after B. It fixes 2021 day 15 and 2020 day 15 with no
  source change, and keeps to `hoist.rs`'s "only what's cheap to keep" rule.]
- **D2884: Computed fields stay out of the type's hash, as field defaults do?** [rec: yes.
  They change how values run, not what the type is to the kernel. The runtime image's
  key covers the layout.]
- **D2885: Rule out a user-written `implemented_by`, and identity-keyed memoisation, for
  this purpose?** [rec: yes. The first is an unchecked second body, a trust hole the
  kernel can't see. The second can give wrong answers under in-place reuse, and its cost
  depends on what the optimiser happened to do.]

## 8. Tickets to file

In order. Stage 0 can run alongside stage 1.

1. **Stage 0a: guide section "Keeping a derived value"** (`docs/guide/11-running-and-shipping.md`,
   Performance notes, or the records chapter). It covers the slow method, the `let` outside
   the loop, and a constructor function, with examples checked. B's syntax is added
   when stage 1 lands. DeepSeek, 30 min. Tests: the guide example check
   (`crates/cli/tests/tools/guide.rs`), by `task test:one`. **Absorbs SW-1576's guide half.**
2. **Stage 0b: profiler hint, a function called many times on few distinct values.** In
   `crates/rt/src/profile.rs`, count the distinct first runtime arguments per row, by
   pointer, in `--profile` runs only. Report rows over a threshold in the summary. Sonnet,
   60 min. Tests: the profiler's unit tests, and one new example with a method that
   rebuilds a `Map` (by `task test:one`). **Replaces SW-1576's lint half.**
3. **Stage 1a: computed fields, elaboration** (Opus: core language). Parse `computed f:
   T := e` in a record's braces. Generate `T.f` as a plain definition, with
   `FieldDefault`-style captures. Errors for literals, patterns, cycles, and computed
   fields on types with several constructors. `syntax.md`, the guide, `stitchwort fmt`.
   Opus, 90 min. Tests: new `examples/accept/computed-field*.sw` and
   `examples/reject/computed-field-*.sw` via `task test:one -- examples`, fmt
   round-trip, `snap:hashes` and `hash_stability` for the new examples.
4. **Stage 1b: computed fields, runtimes** (Opus: lowering trust). The hidden slot in
   machine and JS lowering, filled at every construction path. `T.f` gets a run body
   that reads the slot. An update copies the slot when it doesn't touch the captures.
   The JS decoder fills it. Opus, 90 min. Tests: `examples/extract/computed-field.sw`
   (`-- run:` cases on the machine, `--native` and `--js`, against `--reference`), and
   the extract `bound_to_the_prelude` tests if lowering of std constructors is
   touched.
5. **Stage 1c: use it in 2020 day 19** (§5): drop `matchesCompletelyIn`, restate
   `tableRule`. Then, if they read better, use it in 2020 day 15 (`count`) and 2021 day 15
   (`height`). Sonnet, 45 min. Tests: `task test:one -- year2020_day19`, `audit:touched --
   Aoc.Year2020.Day19`; the same for days 15. **Closes SW-1602** (unless stage 2 lands
   first).
6. **Stage 2: C-narrow hoisting** (after stage 1, independent of it). A shared pass over
   run bodies, next to `hoist.rs`, with §3.3's four rules. Opus, 75 min. Tests: unit
   tests of the pass (each rule's negative case: under a branch, a `List` result, a
   variable bound inside), and `task test:one -- year2021_day15` with the `let` workaround
   reverted in a scratch copy, timed before and after.

Not covered: the 2021 day 9 kind (erasing data used only by proofs). It needs its own
note, and doesn't belong here. Recursive and several-constructor computed fields
(Lean's hash-at-every-node use) wait for a day that needs them.

# Proposal: what the backends trust

**Status:** draft 1, 7 November 2026. Ticket SW-1893. Design only: nothing here is built.
Decisions D2711 (asked by the js/native review) and D2790 to D2791 ([§6](#6-questions-for-matt)).
Builds on three reviews of 7 Nov: `docs/reviews/code-review-rt.md` (F3),
`docs/reviews/code-review-js-native.md` (N2, N3) and `docs/reviews/code-review-core.md`
(F2, F16), and on §1.3 and §3 of the 1 Nov review (`docs/research/rust-codebase-review.md`).
Their findings aren't repeated here. Code was read on `lane/SW-1893` at `e35f954ad`.
Nothing was built or run.

**The short answer.**

1. **Native code.** Native compilation takes a single value, `Prepared`, which only
   lowering can make. It holds the program and its image, made together. Arities then
   agree by construction, and the standalone executable's tables are made from the same
   value. Native code also checks a value's shape before it reads one of its fields.
   That costs a compare on words already in registers, with no extra memory read. So a
   lowering bug stops the run with an internal error, as on the machine, and never reads
   memory it doesn't own.
2. **Natives.** Every pinned declaration goes in one table in `crates/core`. That covers
   the kernel's natives, the runtimes' natives and representations, the effect runtime's
   four natives, and the definitions the backends rewrite. Each binding is checked once,
   when the library binds the declaration. A mismatch refuses the library loudly and
   prints the new hash. So an edit to `Nat.sub` or `Effect.bind` fails the very next
   test of any kind, and it can't leave old Rust code deciding equalities or running
   programs.

SW-1885 becomes the first stage of part 2 (§5), not a separate table.

## 1. What a user would hit today

Nothing yet, in either half: the CLI always pairs things correctly, and every pinned
declaration is currently the one its native was written for. These are gaps a future
change falls into without any warning. Each has come close before:

- **A program and an image that don't belong together.** Native compilation is the one
  place in the compiler where a mistake in safe Rust produces machine code that reads or
  writes memory it doesn't own. A test helper that compiles one program and passes
  another's image to `n1::compile`, or that adds to an image's pool as
  `rt/tests/it/linked.rs:35` already does, yields code that may crash, compute garbage or
  corrupt the heap. Rust's rule is that a function not marked `unsafe` must not allow
  that, whatever its caller does.
- **A native outliving its declaration.** On 6 Nov, SW-1558 made one lemma's arguments
  implicit. That changed `Int.decEq`'s hash, so its native quietly stopped binding. The
  extracted JS inlined the match, and the lane's own tests noticed nothing (SW-1582, and
  the memory note on native hash pins). That was the harmless direction. The harmful one
  is when no check exists at all. Suppose a lane edits `Nat.sub`'s body and keeps its
  type: the kernel goes on computing the old body in conversion (`core` F2). Then `rfl`
  proves facts about a function that no longer exists. Suppose instead a lane changes
  `Effect.bind` and keeps its shape: the machine, native code and JS all keep running the
  old semantics (N3).

## 2. Native code: what it trusts today

The reviews established each of these; this table only sorts them by what goes wrong.

| Trusted | Where | On the machine | In native code |
|---|---|---|---|
| Image indices (registers, tables, pool, callees) | `n1.rs` reads `self.vars[r]`, `code.tables[t]`, `image.pool[k]` | panics | **panics the compiler** (Rust indexing while compiling, N2): safe |
| Program and image agree on arities | adapters `n1.rs:786-797` declared with the program's `params`; `sw_apply_cached` (`native_abi.rs:1773`, the check at `:1792`) picks the direct path by the program's arity | n/a (one source) | **wrong number of words in an indirect call: UB** |
| Pool and number tables belong to the code | `TableStore::new(program, &image, …)` `n1.rs:459`; `aot::compile_object(program, image, tables, …)` `aot.rs:75` | n/a | JIT: same image, fine. **AOT: the tables are a separate `&[u8]`**, so a mismatch is built into the executable |
| A register holds a `Data` with enough fields | `Field` `n1.rs:3335`, `Unpack` `n1.rs:4018`, `:4060` | `fields[i]` panics (`machine.rs:1356-1360`) | **reads (and in `Unpack`, frees) through whatever word 1 is: UB** |
| A lambda's body gets a closure of that lambda | `Captured` `n1.rs:3241` | safe indexing | safe *given* the first two rows: closures of lambda L are built by L's `Closure` instruction, whose argument count `validate` checks, and L's code is reached only through a cache keyed by L |

Other values are checked at run time already, from the tag in the register's first word.
That covers reference counting (`owns`, `n1.rs:2647`), the apply cache (`is_tag(v,
TAG_FUN)`, `:3514`) and constructor reuse (`shaped`, `:4140`). A tag outside a `Switch`
table reaches the trap block. Arithmetic, text and array operations go through `rt`
helpers that match on `Value` in safe Rust. I checked these by reading, not exhaustively:
medium confidence that the table above is the complete list of memory-unsafe trusts. The
implementation lane re-audits `n1.rs` for every `load` whose address comes from a
register's word 1.

Two pieces of good news shape the design:

- **Lowering already validates every program** it makes (`lower.rs:185-189`: `optimize`,
  `trmc::apply`, then `validate`). So "made by lowering" implies "structurally valid".
- **`Unpack` already has the field count in a register.** It reads `v.0[2]`, the slice
  length, at `n1.rs:4083`. A `Data`'s three words are the tag byte, the cell pointer and
  the length. Checking the shape is two compares on values Cranelift already holds.

### 2.1 Designs compared

**A. Mark the entry points `unsafe`.** `n1::compile` and `aot::compile_object` become
`unsafe fn`, with the contract "the image is `code::compile(program)`, the program was
lowered from a checked term, the tables are `linked::encode` of both". This is honest
and costs nothing at run time. But it puts `unsafe` at every call site: the CLI's two,
about a dozen in `crates/native/tests` and the standalone tests. That is what the 1 Nov
review warned against ("Do not spread unsafe requirements across otherwise ordinary
runner APIs", §1.3). Each of those blocks would also restate a contract that no caller
can actually check.

**B. Make the image's fields private (the rt review's F3 fix).** `Image` and `Code` get
read-only accessors, so `code::compile` is their only constructor, and native
compilation takes a `Compiled { program, image }`. This closes the pairing hole. It
leaves the shape hole open: `Program`'s fields are public (`ir.rs:66-77`), so safe code
can build an ill-typed program that passes `validate`, compile it, and read out of
bounds (N2). It also touches every read of the image: about 25 in `n1.rs`, plus
`census`, `profile`, `shared` and `linked`.

**C. One value only lowering makes, plus shape checks in the generated code.**
(Recommended.)

- `rt::lower_main`, `lower_global` and `lower_definitions` return `Lowered`, a newtype
  around `Program`. Its constructor is private to `rt`, and it gives `&Program` through
  `Deref`, so the machine, the codec and the JS runner see no change. `codec::decode`
  still returns a plain `Program`, so a decoded program can't be compiled natively
  (D2711).
- `Prepared::new(Lowered) -> Prepared` runs `code::compile` and keeps both. It hands out
  `&Program` and `&Image` and never `&mut`, so `Image` can keep its public fields:
  nothing can change one once a `Prepared` holds it. This is smaller than B. `Image`'s
  pool holds `Rc` values, which can't be changed through `&` (only `Rc::get_mut`, which
  needs `&mut` and a unique count).
- `n1::compile(Prepared, Options)` and `aot::compile_object(&Prepared, &Limits, Options)`
  are the only native entry points. `compile_object` calls `linked::encode` itself, so
  the tables can't come from elsewhere. `TableStore::new` and `Outline::of` stay as they
  are: they are safe data builders, and their only consumer, `Crossing::new`, is already
  `unsafe` with a contract (SW-1124).
- Generated code checks shapes. Before `Field` and `Unpack` read through a register,
  they check that its tag byte is `TAG_DATA` and that its length is greater than the
  largest field index used. Otherwise the code jumps to an internal-error exit: "native
  code took field 3 of a value that isn't a constructor with 4 fields". The machine
  panics on the same input. Both compares use words that are already in Cranelift
  variables, with no extra load, and share one exit per function, so the cost is about
  three ALU instructions and a branch that is always predicted correctly (an estimate,
  not measured; D2790 asks for a measurement).
- `sw_apply_cached` gets a `debug_assert!` that the outline's arity is the code's.
  With `Prepared` they can't differ.

With C, native code's memory safety rests on two things: that `rt` makes a `Lowered`
only by lowering, and that the `rt` helpers and the ABI layout are right, which the rt
review covers. It doesn't rest on lowering being bug-free, nor on the core term being
well typed: a wrong lowering gives an internal error, not undefined behaviour. What C
still trusts is that a well-shaped value means what the program thinks. A lowering bug
that puts a `Pair` where a `Cons` should be gives a wrong answer, as on the machine.

**Cost of C.** One newtype and one struct in `rt`. Call sites change from `program,
image` to `prepared`. The shape checks are a few lines in `n1.rs`. The measurement in
D2790 decides whether they stay on in release builds.

**What C rules out.** Compiling a decoded or hand-built program natively. Nothing does
that today: the standalone executable compiles at build time, from a lowered program
(`cli/build.rs:259`). If it is ever wanted, the shape checks already cover the
memory-safety part. What's missing is a `Prepared::from_decoded` that re-validates, which
is a small addition. So C keeps that option open without building it.

**How other systems do it.**

- Wasmtime makes the same split. `Module::new` validates its input, so it is safe.
  `Module::deserialize`, which loads precompiled code, is an `unsafe fn` because it
  trusts its bytes. A decoded Stitchwort program would be the `deserialize` case.
- OCaml and GHC trust their type checkers in native code: `Obj.magic` and
  `unsafeCoerce` can segfault. Their compilers aren't Rust libraries with a safe API to
  uphold, and Stitchwort's is.
- Lean 4 checks its IR's structure (`Lean.IR.Checker`) before it emits C, and trusts its
  types, as far as I know.

C takes Wasmtime's split and adds the cheap run-time check, because the check is nearly
free here and the machine already behaves that way.

### 2.2 Which checks belong where

| Check | When | Why there |
|---|---|---|
| Structure (slots bound, call and capture counts, constructor arities) | lowering, once: `validate` (`lower.rs:188`) | already done; a `Lowered` implies it |
| Program, image and tables agree | by construction (`Prepared`); no check | nothing to check if only one function makes all three |
| Image indices in range | while compiling: Rust indexing in `n1` | a panic here is an internal compiler error, before any code runs |
| A value's shape at a field read | run time, in generated code (D2790) | the IR is untyped, so no compile-time check can prove it; register-only, so cheap |
| Direct-call arity | none in release; `debug_assert!` in `sw_apply_cached` | impossible with `Prepared` |
| Standalone tables match the code | none at run time beyond `BUILD_HASH` (`linked.rs:412`) | one `build` writes both into one object. Anyone who can edit the executable can edit its code too. Manifest v5's image hash (`native_aot.rs:34`) needn't return |

### 2.3 How we'd know it works

- A `compile_fail` doctest on `n1::compile`, beside the one from SW-1124 (`n1.rs:429`):
  passing a hand-built `Program` doesn't compile.
- A native test that runs a hand-made `Field` on a `Nat` (through a test-only
  `Prepared` from an ill-shaped program, behind `#[cfg(test)]` in `rt`). It gets the
  internal-error exit, the same message as the machine's panic, and no crash.
- The allocation-trace and agreement tests pass unchanged. The checks don't change any
  count.
- A bench run before and after the checks (D2790).

## 3. Natives: one pin table

### 3.1 What exists today

Each kind of binding has its own table (or none) and its own policy:

| Bound | Table | Checked when | If stale |
|---|---|---|---|
| Float's kernel natives, `Float` | `core/float.rs:81` `NATIVE_HASHES`, `FLOAT_DATA_HASH` | when the library binds it (`float.rs:744-757`) | **refuses the library** |
| `+`'s rules R3/R4 | `core/nat_add.rs` `NAT_ADD_HASH` | binding `Nat.addSucc` (`nat_add.rs:220-226`) | silently off |
| Compact text (`List`, `Char`) | `core/chars.rs` | binding | silently off |
| Kernel Nat natives, `natNeq` | **none**: type shape only (`native.rs:395-478`) | binding | **stays bound** (F2); a second registration is accepted and picked by map order (F16) |
| Runtimes' text, int, float natives; `Nat`, `Int`, `Text`, `SafeNat`, `SafeInt` | `rt/natives.rs`: `TEXT_NATIVES`, `INT_NATIVES`, `FLOAT_NATIVES` and five data hashes | every lowering / JS generation | silently off, "slower, but still right" |
| Arrays | `rt/natives.rs:776-822`, `ARRAY_DATA_HASH` | every lowering / JS generation | **refuses programs that load `Array`** (`lower.rs:356`, `js/lib.rs:2330`) |
| Effect natives `bind`, `foldComp`, `translate`, `runPure` | **none**: name, runtime arity, `Comp`'s shape (`rt/effect.rs:133-170`, `js/effect.rs:94-118`) | lowering / JS | stays bound if the shape holds; else silently slow |
| Rewrites: `ifThenElse`, `Decidable.elim`, `toBool` (`rt/lower.rs:369`, `:748-770`), state fusion's `runPure`, `handlePlus`, `ifThenElse`, `Decidable.elim` (`rt/fusion.rs:118-139`), JS's `ifThenElse`, `Decidable.elim`, `Ord.compare`, `Ord.fromCompare`, `List.append`, `Nat.add` (`js/lib.rs:2349-2354`) | **none**: name only | — | stays bound |

The test `crates/driver/tests/library/pinned_hashes.rs` already checks every row above
that has a hash, in one place. It also scans every crate's source for 64-hex literals, so
that no pin escapes it. That is the right instinct, and it is what makes the table
below cheap to adopt.

The kernel Nat natives row is a soundness matter, not just a speed one. Suppose
`Nat.sub`'s body changes and the native stays. Conversion then computes `Nat.sub 3 1`
natively to the old answer. Meanwhile a proof by induction over the new body proves the
new answer. Together they prove `False`. The other rows give wrong or slow programs, not
false theorems.

### 3.2 Designs compared

**P1. Extend each mechanism where it is.** Add a hash table for the Nat natives in
`native.rs` (SW-1885 as filed), another for the effect natives in `rt/effect.rs`
(shared with JS), and another for the rewrites. Each is small, but the end state has
eight tables with three policies. A future native has to guess which one to copy, and
the source scan in `pinned_hashes.rs` has to learn each table.

**P2. One table in `crates/core`, one check, one policy.** (Recommended.)

```rust
// crates/core/src/pins.rs
pub struct Pin {
    pub what: Pinned,                 // Def(Builtin) or Data(Builtin)
    pub hash: &'static str,           // the content hash it was written for
    pub assumed_by: &'static [User],  // Kernel, Runtime, Js: who relies on its meaning
}
pub const PINS: &[Pin] = &[ /* every row of §3.1 */ ];
```

- **The check runs at binding.** `registry::bind_def` and `bind_data`, which every
  library declaration and every check-cache replay pass through
  (`elab/lib.rs:3016`, `cache/mod.rs:2791`), look up the builtin in `PINS`. They hash it
  and compare, in kernel modes. Float's `register_def` does this today, and the check
  replaces it. A mismatch is an `E-BUILTIN` error on the declaration (D2791). For
  example: "`Nat.sub` isn't the declaration the kernel's and the runtimes' natives were
  written for (its hash is now 3f2a…); check each against the change, then update its
  hash in crates/core/src/pins.rs".
- **Backends only ask.** `g.env.builtins().pinned(b) -> Option<DefId>` answers for a
  binding that passed. `rt/natives.rs`'s tables keep their `Builtin → native` columns
  and lose their hash columns. `EffectNatives::new` and JS's `Effect::new` share one
  `rt::natives::bind_effects`, and their shape checks become `debug_assert!`s. The
  rewrites look up `pinned(Builtin::IfThenElse)` and the rest instead of
  `registry().def`. JS's hard-coded `"Yes"` and `"True"` tags (`js/lib.rs:5323-5338`)
  read the registry, as `decision_yes_tag()` already does.
- **The kernel keeps its own guard.** `register_native` refuses a definition whose pin
  didn't pass. It also refuses a second registration of the same `Native`, and stores
  `Native → DefId` (F16). So the kernel's soundness doesn't depend on the elaborator
  calling it in the right order. Core's own unit tests (`core/tests/it/glue.rs:188`)
  register a hand-written `Nat.add`, so they need a `#[doc(hidden)]` registration that
  skips the pin check and is used only there. The lane decides the exact form.
- **Groups stay groups.** The effect four, with `Comp`, and the eight array natives,
  with `Array`, are all-or-nothing. With refusal at load this happens by itself: any
  stale member refuses. The fallback below keeps the grouping explicit (`group:
  Option<Group>`).
- **There is a fallback, but only for tests.** Four extract tests deliberately change
  the prelude to check that a stale native falls back correctly
  (`extract.rs:4622-4806`). A `#[doc(hidden)]` session option, `StaleNatives::FallBack`,
  turns a failed pin into "unbound". It is used only by `Session::with_prelude`'s
  callers. The fallback code paths exist anyway, because the differential tests turn
  natives off, so they stay tested.

**P3. Pins in the std source** (`@[native "3f2a…"]` on the definition). This keeps the
hash beside the code it covers. But the person editing std then just updates the
attribute, and the point of a pin is that someone re-reads the Rust native. The pin
belongs beside the native, and P2 puts it beside the error message that names the
native. Lean binds `@[extern]` and `@[implemented_by]` by name, unchecked. Its kernel's
GMP-accelerated `Nat` operations are fixed to the prelude's names (as far as I know).
Both trust the prelude, and Stitchwort is choosing not to.

**Cost of P2.** One new core module of about 150 lines, mostly the table moved from
four places. `bind_def` gains a lookup. The extra work at load is hashing about 80
pinned declarations once per session. Float already does 13 (12 definitions and the type) at load, and hashes are
memoised. I expect a few milliseconds, unmeasured: the lane times `stitchwort check` on
an empty file before and after. Today `bind_text_natives` and `bind_array` hash on
every lowering, so per-run cost may well go down.

**What P2 rules out.** Silently running a changed std declaration "as written" in normal
use. That reverses the policy in `rt/natives.rs`'s header, "slower, but still right" (D2791). It also
means a lane that edits a pinned declaration can't run anything until it repins. That is
the point, and the refusal prints what to paste.

### 3.3 How the existing tests fit

- **`pinned_hashes.rs`** becomes the table's test:
  1. every `PINS` entry applies to the full library, listing every stale one at once,
     whereas the load refusal stops at the first;
  2. no 64-hex literal appears in any crate's `src` outside `pins.rs` (its scan,
     narrowed);
  3. new: every `Builtin` that `crates/rt`, `crates/js` or `crates/native` look up
     (`loaded_def(Builtin::…)`, `registry().def(Builtin::…)`, `loaded_data(…)`) is in
     `PINS`, or in a short allow-list with a reason. For example, `CompIn` is used only
     to recognise a type, and `pretty.rs`'s lookups are for printing only. That makes
     the rule enforce itself, so the next native can't skip it.
- **extract's `*_bound_to_the_prelude` tests** (`extract.rs:3211-3330`), float's
  `the_float_bindings_are_the_pinned_declarations` (`driver/tests/elaboration/float.rs:62`),
  `nat_add_is_the_pinned_declaration` (`driver/tests/proofs/nat_add_rule.rs:102`) and
  `compact_text_is_bound_to_the_prelude` (`driver/tests/projects/compact_text.rs:990`) all
  become redundant. Every session now refuses a stale library, and `pinned_hashes`
  covers the rest. Delete them. SW-1586 (make a lost native loud) is closed by this,
  and the brief rule in the "native hash pins" memory note can go.
- **The four changed-prelude extract tests** keep their meaning, under
  `StaleNatives::FallBack`, plus one assertion that the default refuses.
- **The `hash_stability` snapshots** are a different guard. They show that an
  elaborator change left every declaration's hash alone, so they sit upstream of pins.
  When they change, `snap:hashes` is reviewed as now. If a pinned declaration is among
  them, the library refuses to load until it's repinned, so the two can't drift. The
  pins can't be derived from the snapshots: a pin is a person's statement that the
  native was re-checked, and copying hashes would skip that. `task pins:show` prints
  the table with the current hashes, to paste after checking. It never writes the file.

## 4. What it should do, and how we'd know

- Changing `Nat.sub`'s body in std makes `stitchwort check` on any file fail, with one
  error naming `Nat.sub`, its new hash and `crates/core/src/pins.rs`. A test does that
  with `with_prelude`.
- Changing `Effect.bind`'s body (same type) does the same, naming the runtimes and JS.
  Today it's silent.
- Making a lemma's arguments implicit, as SW-1558 did, fails the lane's own tests at
  once, wherever they are. On 6 Nov it took a merge and four failing tests on `main` to
  notice.
- Compiling natively from anything but a lowered program doesn't type-check, and a
  hand-made ill-shaped program stops with an internal error, not a crash.

## 5. SW-1885: build it from this note

SW-1885 (pin the Nat natives, refuse a second registration) is the kernel half of P2.
Built as filed, it would add a sixth table that stage 4 then moves. Built from this note,
it creates `pins.rs`, with the kernel's entries first: Float's, `+`'s rules, compact text,
and the ten Nat natives with `natNeq`. The runtime and JS entries follow in the next
stage. It's the same lane size (Opus, about 60 min), and it lands first because it's the
soundness-critical part. That is sequencing, so I've decided it. SW-1885's body already
absorbed D2710 (the effect natives and rewrites), and that part becomes stage 4.

## 6. Questions for Matt

- **D2711 (from the js/native review): should native compilation accept only programs
  lowered in this process, enforced by a type only lowering makes?** [rec: yes. Nothing
  compiles a decoded program natively, the standalone path compiles at build time, and
  with D2790's checks a later `Prepared::from_decoded` would be a small, safe addition
  if it's ever wanted.]
- **D2790: should native code check a value's shape at every field read (tag and field
  count, both already in registers), so that a lowering bug stops with an internal
  error, as the machine does, instead of reading memory it doesn't own?** The cost is
  estimated at about three instructions and a well-predicted branch per field read. The
  lane measures it on the bench. [rec: yes, on in release, if the bench shows at most
  2%. Otherwise on in tests and debug builds only, and memory safety then also rests on
  lowering. I expect well under 2%.]
- **D2791: when a pinned declaration changes, should the library refuse to load (an
  `E-BUILTIN` naming it and its new hash), for every pin: the kernel's, the runtimes',
  the effect natives and the backends' rewrites?** Today this differs by kind: the
  library refuses for Float, programs using `Array` are refused, text and integer
  natives are dropped silently, and the Nat and effect natives and the rewrites keep
  running the old code. Refusal only ever affects someone editing std, since user code
  can't bind a builtin. A hidden option keeps the fallback for the tests of the
  fallback. [rec: yes. It replaces the silent "slower, but still right" fallback, closes SW-1586, and turns the
  `core` F2 soundness gap into an error.]

Decided here, as implementation detail or sequencing:

- `Image` keeps its public fields: `Prepared` gives out only `&`.
- `aot::compile_object` encodes the tables itself.
- The pins table lives in `crates/core`, because the kernel needs it and core can't see `rt`.
- `task pins:show` prints the table and never writes it.
- SW-1885 is built from this note (§5).

## 7. Tickets to file

In order. Stages 1 and 3 touch different crates and can run side by side. Stage 2
follows 1 (both in `n1.rs`), and stage 4 follows 3.

1. **`Lowered` and `Prepared`; native entry points take them** (§2.1 C, without the
   shape checks). Opus, 60-75 min (unsafe boundary). Replaces SW-1893's implementation
   half, and the rt review's lane 3. Covers: `Lowered` from `lower_*`;
   `Prepared::new`; `n1::compile(Prepared, …)`; `aot::compile_object(&Prepared, &Limits,
   …)` encoding its own tables; call sites in `cli/main.rs:2997`, `cli/build.rs:259`,
   `crates/native/tests`, `crates/standalone/src/aot/tests.rs`; the `compile_fail`
   doctest; the `debug_assert!` in `sw_apply_cached`. Tests:
   `task test:one -- -p stitchwort-native -E 'test(/object|relocatable|keeps_its_image/)'`,
   `task test:one -- -p stitchwort-standalone aot`, `task test:one -- -p stitchwort-rt
   linked`, and the doctests of `stitchwort-native`.
2. **Shape checks at field reads** (§2.1 C, D2790). Opus, 45-60 min, after stage 1.
   Covers: `Field` and `Unpack` check the tag and length into a shared internal-error
   exit; re-audit `n1.rs` for any other load through a register's word 1; a test of an
   ill-shaped program on the native runner; a bench comparison (`crates/bench`, the
   field-heavy programs) recorded on the ticket. Tests: the new test, `alloc_trace` and
   the agreement tests in `crates/native` that touch `Unpack`
   (`task test:one -- -p stitchwort-native -E 'test(/unpack|reuse|agree/)'`).
3. **SW-1885, rescoped: `core::pins` with the kernel's pins** (§3.2 P2, §5). Opus,
   60 min. Covers: `pins.rs` with Float's, `+`'s, compact text's and the Nat natives'
   and `natNeq`'s entries; the check in `bind_def` and `bind_data`; refusal at load
   (D2791); `register_native` refusing an unpinned or second registration, with
   `Native → DefId` (F16); the test-only registration for `core/tests/it/glue.rs`; a
   `with_prelude` test changing `Nat.sub`. Tests: `task test:one -- pinned_hashes`,
   `task test:one -- -p stitchwort-driver float`, `task test:one -- nat_add_rule`,
   `task test:one -- -p stitchwort-core glue`, `task test:one -- prelude_errors`.
4. **Backend pins: runtimes, effects, rewrites** (§3.2). Sonnet, 75-90 min, after
   stage 3. It spans `rt`, `js` and `core`, but each piece follows stage 3's pattern.
   Covers: `rt/natives.rs`'s hashes moved to `PINS`; `bind_effects` shared by `rt` and
   `js`; the rewrites through `pinned(…)`; JS's tags from the registry;
   `StaleNatives::FallBack` for `with_prelude` sessions, with the four changed-prelude
   extract tests moved onto it. Absorbs the D2710 half of SW-1885 and closes SW-1586.
   Tests: `task test:one -- pinned_hashes`, the four `a_changed_*` extract tests,
   `task test:one -- -p stitchwort-rt effect`, `task test:one -- effect_runtime`.
5. **One pin test** (§3.3). DeepSeek, 30-45 min, after stage 4. Covers: the scan in
   `pinned_hashes.rs` narrowed to `pins.rs`; a new scan of backend `Builtin` lookups
   against `PINS` and an allow-list; deleting the redundant `*_bound_to_the_prelude`,
   float and nat_add pin tests; `task pins:show`. Tests: `task test:one --
   pinned_hashes`, and the scan shown failing on a deliberately unpinned lookup, then
   reverted.

Not covered here: the rt review's other native findings (F1/N1's `Array.replicate`
cost, F9's debug checks in `sw_empty_cell` and `sw_free_emptied`, SW-1894), which sit
beside this boundary rather than on it. Also not covered: the macOS JIT write-protect
state (1 Nov §4.3), and the kernel's other public state (D2641, SW-1888). The latter is
the same idea of a type only the trusted side can make, applied to kernel admission;
stage 1's `Lowered` doesn't depend on it.

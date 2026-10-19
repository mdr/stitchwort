# History

What has been done, moved here from `TODO.md` when the task list became the
kanban board (`board/`, see [board/README.md](../board/README.md)) on
19 Oct 2026. The text is verbatim: git log has the full commit history, and
open items now live as tickets.

## Recently done

- `55c48eb` Char-pattern arms keep the equation: in an arm for `'a'` the matched character is the literal (the proof field is transported to `rfl` with `J` and `Bool.uniqueEq` where the goal or a hypothesis mentions it), so `| 'a', h => rfl` proves `c = 'a'`; `examples/accept/char-pattern-proofs.sw`.
- `df63a82` Fixed a compiler panic after a failed record type (failed data groups now resolve as failed), and `else`/`then` on their own lines continue an `if`.
- `d567dfc` Playground: warnings shown apart from errors, a phone layout (viewport, no sideways scroll), the JavaScript tab shown in full; 21 browser tests.
- `6a790a1` `Partial` stage 1: `{Partial}` in types; partial groups translated into ordinary checked declarations over an opaque `Delay`; the runtime steps them (one tick per recursive call, matching `crates/partial-model` trace for trace); `main` can loop until end of input; total code can't run partial code; JS erases `Delay`.
- `22d7b01` Records stage 1: declared records (`type Person = { name : Text, age : Nat }`), `p.name`, `{ p | age = … }`, record patterns, dependent and proof fields, evaluation order as written, derived `==` where provable; JS plain objects with proof fields validated at the boundary; every data type's hash now includes its field names.
- `1965faf` Compact text stage 2: text literals are one compact term in the kernel (shared character ranges), indistinguishable from the list they stand for; long literals from ~1,800 (2 MiB thread) to over 4 million characters; a build fingerprint and modes in the test-cache key; ~28,000 whole-result comparisons and mutation evidence.
- `1c2addc` Mutual recursion stage 3: mutual data types (`Tree`/`Forest`, `Even`/`Odd`, three-member groups) checked as a unit; positivity across the group (`Bad1`/`Bad2` refused; the mutant proved `Void`); no data from `Prop` groups; group hashing; million-deep `Tree`/`Forest` across the JS boundary. Mutual recursion is complete.
- `358fec5` `Partial` draft 3 (stage 1 only; later stages someday/maybe) and `crates/partial-model`, an executable model of the stage-1 runtime running the reviewer's test table.
- `af02abc` Mutual recursion stage 2: declarations in any order within a file, function groups checked as a unit by the kernel (`define_group`), witness messages naming each member, group hashing, `auto` diagnostics explaining unavailable candidates, one JS calling convention; mutation evidence including the Rocq-bug shape.
- `73899f9` Playground polish: 18 headless-Chrome tests (`nix develop -c ./web/test.sh`), streamed run output (Stop keeps what was printed), Tab/undo and resize fixed, `E-INPUT` after 10,000 reads past end of input.
- `01208f2` Natives match their definitions as whole results, proofs included: `decEqNat` redefined so its `No` proof is small and the native returns exactly it (new native `eqNatSound`); every native audited; natives-on/off whole-result tests including numbers above 2^64.
- `9eb1487` Size-change termination for single definitions: Ackermann, swapped arguments and `merge` accepted; partial recursive calls refused with a suggested lambda; one shared entry arity; compared with the old checker on 20,000 generated programs (the new one accepts all the old one did except 7 partial calls).
- `4776303` JS boundary follow-ups: decoders read only own properties (blocks prototype pollution), shared input decoded once (a 60-level DAG went from never finishing to instant), the generator refuses a definition without a body, DESIGN's boundary table matches what's built.
- `813fe74` Number patterns: a number switch in kernel case trees; the 256 cap is gone (`statusText 404` works, 10^30 too); `f 256` checks in 0.01 s instead of 2 s; 3 columns × 5 keys from 85 s to under a millisecond; constructor-expansion oracle over 300 generated definitions.
- `72d3004` Mutual recursion phase 1: draft 3 of the design and the size-change graph algorithm (`sct.rs`), with an independent reference implementation and mutation evidence.
- `afad1e0` Kernel admission ([kernel-admission.md](proposals/kernel-admission.md)): declarations are pending, final or failed, and may refer only to final ones; closes a split cycle (`f 0` looping) and `impossible MakeD : Void` via the raw kernel API; 11 must-reject tests.
- `f31d1c9` Compact text stage 1: `Text` is a JS string in generated code with 14 native operations bound to the prelude definitions by hash; prelude text operations handle over 4 million characters in Node (from ~5,000–8,000).
- `84bc590` JS boundary hardening: names can't collide by construction (field `tag` becomes `$tag`, exports aliased, reserved names refused), iterative codecs (a million-element list in about 0.2 s), clearer boundary errors.
- `07550ff` Recorded benchmarks (`crates/bench`, `bench/baseline.toml`): deterministic counts (steps, visits, allocations, peak heap) checked in `nix flake check`; timings reported, not checked.
- `017d554` Text step 3 (js-text lane, merged): `Text` and `Char` as JS strings with strict decoding, parameterised data types at the boundary, self tail calls as loops, `StitchwortResourceError`.
- `ccebba3` Syntax colouring in the playground's editor (CSS Custom Highlight API, with a fallback); restoring the saved draft on reload fixed.
- `d166039` Stack-safe step 4 (depth-guards lane, merged): every recursive pass guarded by stack use; deep nesting is `E-RESOURCE` natively and in WebAssembly (`crates/driver/tests/nesting.rs`).
- `f35f1a7` Text step 6 (playground-run lane, merged): the playground's Run button and its compiler in Web Workers, replaced after a crash. View it locally with `web/serve.sh`.
- `65f91ce` Text step 5 (run lane, merged): `main` and `stitchwort run`, tested against `simulate` and real standard input and output; `examples/accept/adder.sw`.
- `3fb4764` Text step 4 (IO lane, merged): the `IO` ability and `simulate`, `examples/accept/io.sw`, `examples/extract/io.sw`.
- `fae5cc2` Stack-safe step 3: `conv`, `unify` and `quote` as work lists; iterative freeing of terms.
- `78a9ddc` Local WebAssembly test page: `web/stress.html`, served by `web/serve.sh`.
- `5caa024` `unsafe` allowed with a written justification (lint `deny`, was `forbid`).
- `cdfae0d` Stack-safe step 2: the abstract machine, the reference evaluator, differential tests, iterative freeing of values.
- `14ac90d` Every sub-term the evaluator runs is behind its own `Rc`.
- `2942e55` Checking computes an argument only when a type needs it.
- `e53c53f` Stack-safe step 1: resource errors and per-operation budgets.
- `02235d8` Constructor fields shared (fixed quadratic list recursion).
- `0878284` Text step 2: `Text`, its operations and laws, `++`.
- `01313d1` Text step 1: `Char`, literals and escapes.

## Status notes archived from TODO.md (19 Oct 2026)

The "Now" and "Next" sections as they stood when the board replaced them.
Open items in them were also turned into tickets (some excerpts overlap).

### Now

**In flight (19 Oct, late afternoon) — for whoever picks this up after a context compaction:**
- DeepSeek (OpenCode Go, `opencode run --agent worker --model opencode-go/deepseek-v4.1-flash`) tasks, each in a remote-free scratch clone; specs and logs in the session scratchpad `tasks/` dir (`<name>.txt`, `<name>.log`, `<name>.dir`):
  1. `fuzz`, `cycle`, `hash`, `zip3`: merged and gated (see Recently done).
  2. `hlweb`, `hlvscode`: merged and gated (interpolation colouring; VS Code extension 0.0.2 installed locally).
  3. `reuse` — crates/web keeps the last checked Session for check/test/extract of the same source (first Tests visit checks once). Clone `…-165906`.
  For each: review the diff (DeepSeek has introduced real bugs before), check author email, commit in the clone with a "Done by OpenCode with DeepSeek…" trailer, fetch into main, regenerate snapshots/bench, gate (in the background), browser tests for web changes (`web/test.sh`, background), update this file.
- Opus char-pattern fix merged and gated.
- Multi-file Draft 3 written (`6ee0888`; user's decisions folded in, new `auto`/instance-search section §4.9); awaiting independent review (prompt in the session scratchpad, with the note inline, on the user's clipboard 19 Oct). User (19 Oct): `check FILE` and `test FILE` use file mode like `run FILE`; `stitchwort` writes `.stitchwort/.gitignore` itself. `auto` ignores sibling files for now (sibling search deferred, revisit with interfaces); interfaces design not started yet (user: not now).
- Playground: stale-worker fix (`9c024a9`) and tab-switch reuse (`5f08d1b`) committed and verified; local server `web/serve.sh --no-build` on port 8000 (no-store headers).
Design note `docs/proposals/let.md` written (recommends a kernel `let`
that keeps its value, Rocq/Lean style, after a step 0 that stops treating
every `let` as effectful). Reviewed; the user accepted (19 Oct): option
A, step 0 first, no `have`, pattern lets via projections, pair eta as its
own note, `grid.rolls` fix in step 0. Lane `let-note-rev` folds the review
in; then build in three Opus stages, one at a time: (1) step 0; (2) kernel
`Let` + metavariable audit; (3) lifting with re-created lets, termination,
erasure, JS, pattern lets.
`let` stage 1 merged (`f1255e8`: proof lets work, no `runPure` in pure
code, `grid.rolls` after an IO `let`; day 2's `pickIf` gone). Stage 3
also: written type when the value is itself an effectful call
(`let g := Grid.read ()`).
AoC days 1-5 reshaped (user, 19 Oct): `parseX`, `solvePart1`,
`solvePart2` on the parsed input, combined in `main`; day 1 `part1`/`part2`
are `zerosLandedOn`/`zerosPassed`, `Dial.wrap` is `Dial.fromInt`; day 5
has a `Database` record.
Design note `docs/proposals/checker-evaluation.md` merged (the checker
recomputes values it doesn't need: `print` args, dot notation, `==`/`if`,
proof fields; (a) bind instead of evaluate, in the elaborator; (b) lazy
values while checking; (d) glued values). Reviewed; the user accepted
(19 Oct): do (a) now (1A operation calls and dot notation, 1B `==`/`if`
with fallback); the kernel `Let` value is lazy at check time (contained
thunk, `run` stays strict); decide (b) after re-measuring.
Queued after the current lanes (user, 19 Oct):
- Model tiers (user, 19 Oct; written up in [docs/workflow.md](workflow.md)): Opus (design/analysis/review), Sonnet
  (implementation needing judgement), DeepSeek V4.1 Flash (mechanical
  coding; GLM-5.3-Flash fallback; Haiku mostly retired), via OpenCode Go ($10/mo, `opencode run
  --agent worker --model opencode-go/<id>` in an `opencode-scratch` clone;
  login with `opencode console login`). Rename sweep bake-off (identical,
  correct diffs): DeepSeek V4.1 Flash 1m28s (Go "Global" region on; likely
  China-hosted, ZDR renewed monthly), GLM-5.3-Flash 2m11s, local Qwen3.8
  27B 34m40s (too slow; local is fallback only), qwen3-coder:30b stalled.
  String interpolation (`ede6e54`): DeepSeek, from an Opus spec, 13m20s,
  correct first time apart from one clippy lint (spec now asks for clippy).
  `${e}` is `e.toText` (Text.toText is the identity). Running: fuzz pilot
  (DeepSeek writes crash / native-vs-JS / prove-Void programs; harness in
  the session scratchpad). Later:
  OpenCode 2.0 (`opencode upgrade --major`)
  vs nixpkgs 1.19.
- Option (b) of checker-evaluation.md stays shelved: after the checker
  fixes, AoC days check in 0.11-0.28 s. `if` on a proposition stays partly
  fixed (3 computations, was 4).
- Later (pending user): `List.merge` still doubles on fixed lists with an
  undecidable comparison (0.42 s at 7+7); fixing needs mutual recursion and
  restated sorting proofs. `Text.linesFrom` and min/max folds similar, rare.
- Interfaces design note (Opus, with independent review), Agda/Lean style:
  an interface is a record (laws as proof fields), instances found by
  generalising the `Decidable` auto search; coherence, predictability,
  hashes, namespaces §8. After the current work, before days 6-9 (sort,
  maps, sets; would remove `sum`/`sumInt` duplication). User, 19 Oct.
- Multi-file design Draft 3 written ([multi-file.md](proposals/multi-file.md); files declare namespaces; stitchwort.yaml with source roots); awaiting independent review. User decided: `namespace X` lines, shared namespaces across files, file names meaningless, `stitchwort.yaml` source roots (default `src/`), `run Ns.fn` for any main-compatible function. Also decided (19 Oct): every project file must declare a namespace (E-NO-NAMESPACE, no default); imports per file; cycles between namespaces refused for now; adding to another namespace deferred (needs its own design); test cache in the project folder, gitignored; `run path/file.sw` is always file mode (Std only, needs `main`), `run Ns.fn` is project mode. Draft 3 (19 Oct): decisions folded in, AoC questions parked (§13.2), new §4.9 on `auto` candidates across files and namespaces (compared with Lean, Haskell, Agda, Idris instance search; designed to extend to interfaces); open questions for the user in §13.1.
- Playground (19 Oct, DeepSeek from Opus specs): AoC days 1-5 in the picker with example input (`c65023e`); test results cached like the CLI, "cached"/"ran" per test, "Forget cached results" (`2806ae5`). `Char.toText`, `Bool.toText` (`b707e9f`, found by the fuzz pilot).
- **Char-pattern branches lose the equation:** fixed (`55c48eb`, Opus; see Recently done). Limit: a nested `match` inside a char arm isn't covered (not yet put to the user; proof irrelevance would remove it). The `match h :` report was not a bug (same as Lean).
- DeepSeek batch (19 Oct, from Opus specs, all reviewed): lexer/parser fuzz test `crates/syntax/tests/fuzz.rs` (20,000 cases, fixed seed); `E-SYNONYM-CYCLE` for type-synonym cycles (was E-TERMINATION; found by the fuzz pilot); `NAT_DATA_HASH`/`TEXT_DATA_HASH`, so Nat's and Text's JS representations apply only when the prelude's types hash as expected (extract-js bench allocations +29% from the hashing); `List.zipWith3`. [docs/workflow.md](workflow.md) records the model tiers and hand-off steps.
- Fuzz pilot (19 Oct, DeepSeek, ~65 min): 30 crash probes, 30 native-vs-JS programs, 91 prove-Void attempts: no crashes, no output mismatches, all Void attempts rejected. Harness and briefs in the session scratchpad.
- Fuzz pilot findings to triage (DeepSeek's reports, not yet reproduced): type-synonym cycle reported as E-TERMINATION; non-ASCII identifiers refused (check intent); bare "unknown name" when a parameter is missing.
- Compile-time `include "file" : Text` (contents part of the definition's
  hash, so the existing test cache covers input files; precedents Rust
  `include_str!`, Zig `@embedFile`, Lean `include_str`, Dhall integrity
  imports). Real-input AoC tests in a separate per-day file (e.g.
  `aoc/day04.input.sw`, inputs stay gitignored). User, 19 Oct.
- After `let` stage 3: day 3 back to `let (top, after) := pick ...`; day 1
  `zerosPassed` as `turns |> .scanLeft Dial.move start |> .zipWith
  Dial.zerosDuring turns |> .sum` (check `zipWith` argument order), with
  its proof reworked (Opus).

Merged 19 Oct: `run --js` (`9f905c9`; day 4 17 s -> 1 s; Partial works;
2 GB worker stack, user: keep as default), `let` stage 2 (`48bac44`: kernel
`Let`, value computed on demand while checking, strict when running).
AoC example answers are now tests; `theorem` only for all-input facts.
`let` stage 3 merged (`0c5e2fb`): lets are transparent to the checker,
re-created in lifted helpers, proof lets erased, pattern lets are
projections outside proofs. Leftovers: pattern lets in proofs stay
`match`; projections give termination no smaller-than evidence; deferred
values recomputed per force.
AoC rewrites merged (`ed41604`): day 1 part 2 is scan-and-zip (proof
simpler: no accumulator), day 3 uses `let (top, after) := pick ...` (no
proof change).
Checker fixes merged (`abc53d0`: result types cached for the Decidable
search; `List.filter`/`count` write their rest once; day 2 checks in 0.28 s,
was 0.71 s; §9.5). Day 2 profile merged (checker-evaluation.md §9: option
(b) shelved). Local model set up (ollama + qwen3-coder:30b + OpenCode
with safeguards, ~/.config/nix-darwin/opencode.nix); Claude orchestrates
it. (Syntax polish merged: `type Grid = List (List Nat)`, lines may start
with `,` or a closing bracket, trailing commas, char-match errors name
characters). Checker fix (a) merged (`1fc7824`: print/dot/==/if no
longer compute closed values at check time; day 1 check 1.11 s -> 0.58 s).
`run --js` (user, 19 Oct): compile `main` to JS, run under Node with an
IO driver and a big stack. Quick wins Q1/Q2
(native lookup by index, mimalloc) skipped (user).

Queued after the `let` fix (user, 19 Oct): prove day 2's block-walking
spec equals ID-walking (the puzzle's wording, the user's Scala). Partly
to find out what makes such proofs hard and improve Stitchwort for it.
Also after the `let` fix: prove day 5 part 2 equals the brute-force count
of covered ids for every input (merged ranges sorted and disjoint, merging
keeps coverage). Example `rfl` checks are unit tests, not proofs (user).
Deferred (user, 19 Oct): list helpers and days 6-9 until the user is
happy with the learnings from days 1-5. `[x, ..rest]` list patterns merged (tail may be any
pattern; `[..p]` is `p`; not in list expressions).

Merged overnight (18-19 Oct): day 3 proofs (`best` is a subsequence, has
length `min k (length ds)`, and is optimal; 9 prelude lemmas incl.
`List.Subsequence`), char patterns (`| 'L' =>`), days 6-9 capability
survey (docs/aoc-2025.md sections 8 and 10), day 4 (`aoc/day04.sw`, both
answers right, 16 s), day 5 (`aoc/day05.sw`, both answers right,
0.9 s; `rfl` checks on the example; merge sorted-and-disjoint not proved),
day 2 proofs (`62938b2`: `repeatedCorrect`, `part1Correct` against
block-enumerating specs; part 2 brute-force cross-check on 160 ranges;
31 prelude lemmas). Inputs for days 4-9 fetched from the user's Scala
repo into `aoc/inputs/` (ignored).

Day 1 review batch merged (`a89c5bd`): `Dial.place` gone from the
implementation (kept as a proofs-only abbreviation beside the proofs:
substituting `Int.modNat e (Succ m)` broke four lemmas with "expected" and
"actual" types that print identically, cause not investigated), `Dial.size`,
`turnOf` as a char `match`.

Waiting on a decision (for the morning):
- Proof `let`s (from day 3): a `let` is opaque to the checker (after
  `let p := 10 ^ n`, a proof about `p + 1` doesn't see `p`'s value), and
  a `let` can't bind a proof (`E-UNIVERSE`). Being fixed (let stages).
Repo published (19 Oct): https://github.com/mdr/stitchwort, public, MIT;
`origin` uses the `github.com-mdr` SSH host. Push only when asked.


### Next

In this order, after the in-flight lanes finish (the user: build a
capability we know we'll need before the work that needs it):

1. **Namespaces** (lane `namespaces-design`, docs only, in progress): the
   user decided qualified names (`List.sort`) and dot notation by type
   (`xs.sort`); `import List (map, filter)` for specific names only at first,
   meaning the same for namespaces now and files later; a small set of
   default-visible names (core types, constructors, operators); prefixed
   names removed. Design note written
   ([namespaces.md](proposals/namespaces.md) draft 1, `Std` root,
   stage 0 binds built-in syntax to fixed library definitions first). The
   user answered §11 (implicit opening inside a namespace and extending
   library namespaces from user code are deferred; shadowing a type hides
   its default constructors). Reviewed: approved, with clarifications. Draft 2
   and stage 0 (built-ins bound to fixed declaration identities) merged as
   `06c78d2`. Stage 1 (namespaces, qualified names, `import`, the prelude
   in `Std`, every example rewritten) merged as `46d6578`. Stage 2 (dot
   notation by type, `e.f args`) merged (`dc201e6`); decisions in
   namespaces.md §9 "As built". Follow-ups: narrowing of speculative
   dependencies (mitigation 2); rewrite examples to dot notation; §5's
   mixed-kind example is accepted (records get no speculative edges;
   the user agreed); `xs.map` needs list functions in `Std.List`. Noticed, not investigated: a signature
   `Comp NoOp NoRes Nat` behaves like `Nat`.
   Alongside, for Advent of Code: lane `aoc-survey` (Sonnet) surveys days
   1–5 of AoC 2025 from the user's solutions and inputs to rank what the
   library needs (merged: [aoc-2025.md](aoc-2025.md)); the `Int` design
   note is written ([integers.md](proposals/integers.md) draft 1: `Int` as
   a data type over `Nat`, no kernel change, Euclidean `/` and `%`); three
   questions answered (Euclidean `%`, `-x` on any expression, `%` on `Int`
   gives `Int`). Reviewed: approved (no kernel change; revise operator and
   literal typing first). Draft 2 merged (`3d8aa9d`): two-pass group rule
   for number types, prefix-minus rules, a 7-stage plan split Opus/Sonnet.
   Stage 1 (the type `OfNat | NegSucc`, its library, `Int.decEq`, three
   division conventions, `Text.toInt`, lemma checkpoint 1) merged
   (`d3753f8`); `OfNat`/`NegSucc` are visible unqualified (the user: fine for
   now; hiding a default type's constructors would need a namespaces
   mechanism). Stage 2 (prefix
   minus `-e` and patterns `(-k)` in the parser; the elaborator says "not
   yet supported") merged (`220dedc`). Stage 3 (number literals and the
   group rule, `numbers.rs`; "old way first" for equations and nested
   effectful arithmetic keeps every hash unchanged, pinned by
   `hash_stability.rs`) merged (`db1e2a2`). The user accepted "old way
   first", the three reworded messages, and polishing two messages
   later (`int-binding-nat` should say `m` is a `let`-bound `Nat`;
   `rfl` rejections print `Int.mod x 3`, not `x % 3`). Stage 4 (integer
   patterns, `-k` and `k` in `Int` columns, missing-case errors name
   integers) merged (`9cb1d72`). Small polish for later: "a `Int`" →
   "an `Int`"; the default's note should suggest `OfNat Zero`/`OfNat
   (Succ k)` for `Int`; `f Zero = …; f 0 = …` points at the wrong row.
   Stage 5 (JS: `Int` as `bigint` of either sign, strict boundary
   codec, 23 natives, two hash fallbacks — the type's hash switches the
   representation, each native is bound by its definition's hash)
   merged (`3ef9015`). Stage 6 (`Int.divAddMod`, remainder bounds,
   `Int.modNatLt`, the `%`/`modNat` link; examples `int-dial.sw`,
   `int-grid.sw`) merged (`c49d2bc`). Not done: division laws for the
   truncating and flooring pairs. Next: stage 7, docs (DESIGN.md,
   syntax.md, core.md; Sonnet).
   Tuples print as `(a, b)` (`5f11367`). `==` works on lists,
   tuples and `Maybe` (`57392bd`): `auto` builds the element decider
   itself (depth bound `MAX_DEPTH = 8`); records with such fields may now
   get `==` too (untested on its own). `Nil == Nil` with an unknown
   element type is still `E-AUTO-NONE`. Effectful callbacks for
   `map`/`filter`/folds: later, when a program needs them.
2. **Standard library for real programs** (ranked by the AoC survey,
   [aoc-2025.md](aoc-2025.md)). Done: the list toolkit (`map`,
   `filter`, folds, `sum`, `zip`, `take`/`drop`, `get`, …) and `Nat`
   min/max/absDiff/pow (`51ce453`; callbacks are pure for now — no
   effect-row convention yet). `Nat` arithmetic lemmas merged
   (`9871787`: add/mul laws, order, subtraction, `divMod` and `modLess`
   with an explicit `d != 0`; not yet min/max/absDiff facts). To do: a
   `readAllLines` helper, `Nat.digits`, sorting with a correctness proof (sorted
   permutation), `==` on lists (tests can't compare lists today); later an
   `Array` type, a balanced-tree map/set, grid helpers.
3. **Syntax conveniences**: design note draft 1 merged
   ([syntax-conveniences.md](proposals/syntax-conveniences.md)):
   `where`/local functions and `match` lifted to hidden top-level
   definitions (no kernel change), pattern `let`/lambda, tuple sugar,
   result-type-first checking of calls. The user agreed with every
   recommendation in §8. Reviewed; draft 2 adopts all eleven findings
   (`6c71685`), the user agreed with §9's questions 10–13 too.
   Step 1, tuple sugar, merged (`0a7dbc1`; tuples print as
   `MkPair a b` for now; JS boundary unchanged). Step 2 (result type
   first, one shared undo in `undo.rs`, the `fallback` bug fixed; 12
   example hashes changed, accepted) merged (`f525ae6`). Step 3 (`match`,
   `match h : e`, the lifting machinery in `lift.rs`/`matching.rs`; a
   whole-right-hand-side `match` compiles into the case tree; one `core`
   addition, `Globals::frozen_metas`) merged (`9b9bae8`). Leftovers: a
   lifted `match` in a partial function, a data/ability declaration or
   the REPL is refused. Step 4 (patterns in `let` and lambdas,
   `E-LET-REFUTABLE`) merged (`ec2a784`). Later: annotated lambda
   parameters `\(x : T) -> …` (would also fix the `p.name` hint). Step 5, `where`, waits for the declaration-syntax
   decision below.
   **Declaration syntax (user, 18 Oct): switch to the Lean/Scala style**
   (typed parameters inline, e.g. `def add (x : Nat) (y : Nat) : Nat =
   …`, cases under a signature) instead of Haskell-style separate
   signatures and equations. Draft 1 merged
   ([declaration-syntax.md](proposals/declaration-syntax.md)): the
   parser rewrites new forms into today's, so hashes must stay identical;
   `:=` bodies, `| … =>` cases; a text-editing converter migrates all
   code. The user agreed with all nine recommendations.
   Reviewed (proceed); draft 2 adopts it (`7f13ce7`): exact-arity arms,
   `()` header → `_`, distinct header/implicit names, mixed-style
   declarations refused, multi-layer migration check. Simplified (user, 18 Oct):
   no period accepting both syntaxes. Lane A merged (`db65149`: new parser behind
   `--syntax new` / `Syntax::New`, `stitchwort_syntax::equivalence`
   harness). Lane B merged (`74f3436`: `crates/convert`,
   276 of 280 inputs convert, each checked by AST equivalence; 7 arms in
   5 definitions completed for exact arity). Switch merged (`a32a995`): the
   new syntax is the only one; everything converted; hashes changed only
   for the 5 exact-arity definitions and partial definitions' generated
   `Request` field names (and dependents); tests, error codes and AoC
   answers unchanged. Tidy-up merged (`468a9e4`, `b2a1e14`): docs
   converted, playground colours `def`, browser-test race fixed (21/21),
   `E-ARM-PARAMETER`, "arm" wording, `crates/convert` deleted. The
   conversion is complete. Decided (user, 18 Oct): no `where`; values and
   functions are declared in blocks, top-down, Scala-style (`let x := e`,
   local `def`/`theorem`). Local defs merged (`ddd7b2f`); a merge
   interaction with `&&`/`||` (a condition's undo deleted local-def
   drafts) fixed (`6b57079`). `List.sumBy` added. VS Code extension in
   `editors/vscode` (install with `install.sh`). `&&`/`||`/`not`
   merged (`4b6b29d`: short-circuit on Bool, `And`/`Or`/`Not` on Props,
   `test` accepts a decidable Prop; `if h : p && q` doesn't short-circuit).
   AoC days 4–5 on hold (user, 18 Oct): the user is
   reviewing the day 1–3 code first. Pipe-forward `|>` merged (`d97591a`: value as
   last argument, left checked first so lambdas infer; looser than `=`);
   library main-value-last (`1434622`:
   `Maybe.andThen`, `List.get` reordered; the rest already were). Days 1–3
   rewritten (`0541253`) with the review notes; ready for the user's
   review. Friction from it: a comparison isn't a `Bool` outside
   `if`/`&&`/tests (`List.filter (\n => k * n <= size)`); no `Int` sum;
   `[highest : Nat]` repeated on every `Dial` function; a field and a
   namespaced function may share a name without a warning; no
   `[x, ..rest]` list pattern. Running (user, 18 Oct): method sections merged (`ff2d6ed`: `.f args`,
   `|> .drop 1` is exactly `xs.drop 1`, `people.map .name`; AoC uses
   them);
   comparisons usable wherever a `Bool` is expected,
   `List.sumInt`/`sumIntBy`, and auto-binding of value names used as type
   arguments (`Dial highest`) merged (`95f82a2`, `d4d44c0`, `ddc44f0`).
   The crash-recovery flake was the test's own stack helper (`e08838e`;
   the page was fine). Next small follow-up: check plain lambdas after
   the arguments that fix their type (`List.map (\p => p.name) people`),
   as sections do. (Earlier plan: rewrite days 1–3 with `|>` and the user's review
   changes. Review notes so far: keep `Text.uncons` but write
   `t.uncons` (dot notation) — generally prefer dot notation and
   `rest.toNat`-style calls where they read better; `parseTurn` via
   `andThen` (`t.uncons.andThen (\(c, rest) => rest.toNat.andThen
   (turnOf c))`). `IO.readAll` and `Text.lines` merged
   (`255213d`); `readAllLines` is total and the AoC `main`s are `{IO}`. Day 1 renames: `Pos` → `Dial`, `at` →
   `position`, `ok` → `inRange`, `top` → `highest` (`Dial 99`);
   functions on a type live in its namespace and are called with dots
   (`Dial.isZero`/`d.isZero`, `Dial.move`/`d.move t`, `Turn.parse`). After
   `|>` merges: a small Sonnet sweep making the
   library pipe-friendly — the main value last, Elm-style — starting
   with `Maybe.andThen` (function first, like `Maybe.map`). `>>`/`<<` composition later if wanted; then one switch commit (convert everything, flip
   the parser, delete the old one, hash/AST/test comparison); then a
   tidy-up (docs, playground colouring, awkward converter output); then
   `where`. Header and implicit names must differ. Also queued after the switch: `&&`/`||` and
   a Prop-aware `not`.
4. **Advent of Code 2025, early days** — the medium-term goal.
   **Queued proofs (user agreed, 18 Oct; start after compaction):**
   - Day 3 (Opus, medium): `best k ds` is a subsequence of `ds`; its
     length is `min k (length ds)`; optimal — for every length-k
     subsequence `s`, `fromDigits s <= fromDigits (best k ds)` (with a
     lemma: equal-length digit lists compare lexicographically as
     numbers).
   - Day 2 (Opus, medium; after day 3, both may add library lemmas):
     (a) `r.repeated k n` equals the brute-force sum of ids in `r` that
     are a k-digit block written n times (Gauss sum, digits of
     `base * 10101…`); (b) part 1 equals the brute-force sum of doubled
     ids; part 2's Möbius inclusion–exclusion: no proof, a brute-force
     cross-check test on many small ranges instead. *Done* (a) and (b)
     (`repeatedCorrect`, `part1Correct`; specs walk k-digit blocks, not
     ids) and the cross-check (160 ranges, about 2.5 s); 31 prelude
     lemmas; friction (a `let` before an `if` yields an `Effect.runPure`
     term source can't write) in aoc-2025.md "Proofs (18 October 2026)".
   Lambda postponing merged (`39665ae`: `List.map (\p => p.name) people`
   infers). Plan
   (user, 18 Oct): day 1 done (`aoc/day01.sw`, both answers right,
   0.7 s; `IO.readAllLines`, `Nat.digits` added; friction write-up in
   aoc-2025.md: no `let` patterns (step 4 running), `type Dial = (Nat,
   Nat, Nat)` is a parse error, no `==` for user data types (deriving),
   a duplicate prelude name gives a debug dump without file/line, no
   `List.scanl`). Sorting merged (`8ef0c31`: `List.sort`, `sortBy`,
   `sortWith`, stable bottom-up merge sort, O(n log n), no fuel;
   `Sorted` and counting-based `Perm` proved; 20,000 numbers in 0.7 s;
   not proved: stability, totality of `Text.compare`; new default-visible
   `And`/`Both`); prelude errors now render with file and
   line, `List.scanl` added (`0ff412a`; user programs can no longer
   clash with prelude names since namespaces); `type Dial = (Nat, Nat, Nat)` stays a parse error (user:
   write `Dial : Type`). Automatic `==` for user data types merged
   (`cc94701`, eager, generated `T.%decEq`; skipped for function/proof
   fields, mutual types). Day 1 proved correct (`23c2778`: positions on
   the dial by type; part 2 equals a click-by-click spec). Proof friction
   (aoc-2025.md "Proofs"): fixed since (`30e183a`, `a129404`): proofs and
   types are erased when running (`erase.rs`; tests 10× fewer steps) and
   `Nat.mod` is `n - (n / d) * d` (`% 100` in proofs 20–70× faster);
   still: the checker evaluates proofs inside concrete types, and
   checking evaluates an input-independent `main` print twice; no
   rewriting; (fixed since: `Int` addition laws incl.
   associativity, `Ordering.decEq`, `7f9fc01`). Days 2 and 3 done (`99e806d` 0.15 s, `4f23aec`
   0.45 s; answers right). Fixed since: `if x < y` works on decidable Props
   and list patterns `[]`/`[a, b]` exist (`a48e928`, `8754e6d`). Still
   missing: `&&`/`||` (the lexer rejects `&`) and a Prop-aware `not`; division by a variable
   needs a proof; unreachable `Nil` equations. User OK'd default-visible
   `And`/`Both`; annotated lambda
   parameters later; then days 1–5 rewritten with proofs (deep
   ones for 1, 3, 5 by Opus). `Array`/`Map`/`Set` later (days 4, 8, 9).
   Earlier notes: (decisions in aoc-2025.md: programs
   in `aoc/`, inputs and answers out of git, worked examples as tests), as a stress test with proofs where
   natural (sort correctness, parser round trips, worked examples by `rfl`).
   Inputs: the user's repo https://github.com/mdr/aoc-2025/tree/main/src/main/resources.
   Write up the friction found.

### Closed items from Later and Known issues

- ~~Syntax highlighting of string interpolation~~ done 19 Oct (DeepSeek, merges `887b6b9`, `496a75e`).
- **(Done in stage 1 for JS) The JS limit on text:**
  in generated JS, prelude text operations stop at a few thousand
  characters (`length`, `append`, split, join, `==` aren't tail-recursive),
  with a catchable `StitchwortResourceError`. Measured in Node 22:
  `textLength` about 8,000, `textSplit`/`textJoin` about 5,500, `textToNat`
  about 3,000.
- **Agents' clean-up can hit the user's processes:** the depth-guards lane
  ran `pkill -f serve_forever`, which stopped the local playground server.
  Agent prompts now say to stop only processes they started, by PID.

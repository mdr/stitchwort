# Proposal: hiding std's internal helpers (`@[internal]`)

SW-2008, from the std review's S12 (`docs/reviews/code-review-std.md:340-348`,
D2823). Draft 1, 7 November 2026. Read only: nothing here was built or run.

## 0. Summary

**What a user gets.** Typing `xs.` in the editor, or `stitchwort doc List`,
stops offering `filterStep`, `partitionOnto`, `mapAccumLeftGo` and about 190
other definitions that exist only to make std's functions check or run well,
plus the theorems in std's internal namespaces (`Map.Tree`, `Map.Raw`,
`Omega`, the `ring` syntax types). Proofs keep working exactly as now: a goal
that unfolds `List.filter` still shows `List.filterStep`, and the user can
still write that name in a lemma.

**The change.** One new attribute, `@[internal]`, on a definition or a type
(a type's covers everything in its namespace). It changes what tools *list*
(completion, `doc`, `search`, doc coverage), never what a name *means*: it
isn't an error to use one, the kernel never sees it, and it isn't hashed.

**Why not `private`.** In a prover, a helper leaks into goals by
unfolding, and users write lemmas about what they see. AoC 2020 day 20 proves
`lastReverseOnto` about `List.reverseOnto`
(`aoc/src/Aoc/Year2020/Day20/Proofs/Orientations.sw:12`); three 2024 days
rewrite with `Map.Spec.sameKeySound`
(`aoc/src/Aoc/Year2024/Day06/Proofs/Part2.sw:47`). A `private` that made
those names unwritable would break real proofs, as Lean's `private` does
(§3.4). Hiding from lists gets the benefit without that cost.

## 1. The problem

**In everyday words.** A newcomer types `words.` on a `List Text` and the
completion list mixes `filter`, `map` and `partition` with `filterStep`,
`partitionStep`, `partitionOnto` and `findMapStep`. `stitchwort doc List`
lists them beside the real API. Nothing tells the user which are meant for
them, and once a program calls `List.partitionOnto`, std can't rename it
without breaking that program.

Where they come from, today:

- **Completion after a dot** lists every function of the receiver's
  namespace that takes it, filtering only local definitions
  (`helper_keys`) and generated equations (`crates/elab/src/dot.rs:2206-2207`,
  `2263`).
- **Completion of a bare name** filters the same two
  (`crates/elab/src/nav.rs:1053-1054`).
- **`stitchwort doc NS`** lists every parsed definition, type, interface and
  ability in the namespace whose path has no `%`
  (`crates/driver/src/doc.rs:543-560`); its "did you mean" does the same
  (`doc.rs:522-540`).
- **`stitchwort search`** hides only `%` names, a session's `<…>` names and
  std's `…Example` theorems unless `--all` (`crates/driver/src/search.rs:980-991`).
- **`@[noReceiver]`** (`crates/elab/src/attributes.rs:55-58`) only silences
  `W-RECEIVER-NOT-FIRST`; it doesn't hide anything, and of its 113 uses in std
  many are public API (`Option.map2`, `List.Sorted`, `List.Mem`), so it can't
  be reused as the "internal" mark.

**The constraint: proofs see helpers.** A helper is in the body of a public
function, so it shows up whenever a goal computes:

- 2024 day 13: "the spec's list unfolds to 101 `filterStep`s (the goals
  showed `List.filterStep 0 (List.filterStep 1 (...`" (`aoc/NOTES-2024.md:3911-3913`).
- `List.filter.eq2`, the generated equation users rewrite with, states
  `List.filter (Cons x xs) p = List.filterStep …`
  (`examples/accept/function-equations.sw:135`).
- Users state lemmas about helpers: `List.reverseOnto` (AoC 2020 day 20, two
  theorems), `List.withIndexFrom` (6 app files), `Map.Spec.sameKey` (2024
  days 6, 8, 23), `Map.Raw.Equiv` (the `Quot` examples, e.g.
  `examples/accept/quot-protomap.sw`).

So a design must leave every helper **writable by its full name**, in
programs and proofs, and must print goals that read back.

**The kernel and hashes.** A definition's hash leaves out its own name but a
data type's name is hashed (`crates/core/src/hash.rs:29-33`). Attributes that
don't change the checked declarations aren't hashed (D598,
`attributes.rs:8-11`). Kernel terms refer to definitions by id, not by name.
So anything that only changes listings is invisible to the kernel and the
hashes by construction; anything that renames (a naming convention) changes
the names, and for data types the hashes (migration cost doesn't count, but
it's worth knowing the end state differs only in names).

## 2. What Stitchwort already has

Two hiding mechanisms exist, both for compiler-made or nested names:

1. **`%` names** (`crates/elab/src/scope.rs:92-96`: "No one can write it
   (`%` isn't in names)"): `f.%step`, `f.%match1`, `f.%case`. Hidden from
   `search` and `doc`. They are *unwritable*, and users do meet them in goals
   (`docs/syntax.md:1758`, "a lifted `f.%match1`"), where a proof can't name
   them: the hard end of the scale, and the reason it can't be used for std's
   helpers.
2. **Local definitions** (`docs/syntax.md:341-361`): a `def` inside a body
   is lifted to `owner.name` (`crates/elab/src/lib.rs:2410-2422`), recorded in
   `helper_keys` (`crates/elab/src/state/tables.rs:117-119`), so dot notation
   never finds it and completion skips it, but `owner.name` names it from
   outside, in lemmas too (`docs/proposals/syntax-conveniences.md:574-620`).
   This is the soft end: unlisted but writable. It's what this proposal
   generalises.

Parse-only tooling (`stitchwort doc`, coverage) reads attributes from the
AST (`crates/syntax/src/ast.rs:997-998`; `crates/driver/src/doc.rs:6-10`,
D2143), so an attribute is visible to every listing without a check.

## 3. Designs compared

Criteria: (a) hidden from completion, `doc`, `search`; (b) still writable in
proofs, and goals read back; (c) kernel and hashes unchanged; (d) works across
std's files (the `List` namespace is spread over 12 files in
`crates/elab/src/std/List/`); (e) cost.

### 3.1 A `private` modifier per declaration (hard)

`private def List.filterStep …`: the name resolves only inside its namespace
(or file); elsewhere it's `E-UNKNOWN-NAME`.

- (a) yes. (c) yes, if resolution only. (d) needs "namespace" to mean all of
  `List`'s files, fine.
- **(b) fails.** A goal shows `List.filterStep 0 …` and the user can't write
  it: `lastReverseOnto`, the `sameKey` rewrites and `filter.eq2`'s users all
  break, and a printed goal no longer reads back as a statement. An escape
  hatch (Lean's `import all`, §3.4) puts the name back, so the hardness buys
  little.
- What it is good for is SW-1065: stopping *construction* (§6). That wants a
  hard rule; helpers don't.

### 3.2 An explicit export list per namespace

`exports List (map, filter, …)` somewhere; everything else is internal.

- (a) yes. (b) as 3.1, or as 3.5 if the list only drives listings.
- **(d) and (e) poor.** `List` has several hundred public names across 12
  files; the list would live far from the declarations, every new function
  needs a second edit, and forgetting one hides a public function silently.
  Haskell and OCaml do this per module file; Stitchwort's namespaces are
  open across files (`docs/syntax.md:386`), so there's no one place for it.
  An inverted list ("hide these") is the attribute in the wrong place.

### 3.3 A naming convention tools hide (`_filterStep`, or `%`)

- `%` is unwritable by design (§2): fails (b).
- `_` is a legal identifier start (`crates/syntax/src/lexer.rs:401`), so
  `List._filterStep` would work today with no language change, and tools
  would hide names whose last part starts with `_`.
- (a), (b), (c) yes. But the name is in every goal: `List._filterStep 0
  (List._filterStep 1 …)` is noisier for exactly the users who hit helpers,
  a type `Map._Tree` changes its hash, and the intent is encoded in a
  spelling rather than said. Moving a name between public and internal is a
  rename, which breaks callers: the opposite of what hiding is for.
- Python's `_name` and Dart's `_name` work this way; Dart enforces it
  (library-private), Python only by tool convention.

### 3.4 Lean: `private`, `protected`, simp visibility, the module system

- **`private`** (classic): the name is visible in its file only; the
  constant still exists, goals that unfold to it show it, and other files
  can't write it **[remembered]**. Mathlib's style avoids private
  definitions in anything users prove about for that reason
  **[remembered, medium confidence]**.
- **`protected`**: the name never becomes short through `open`; it must be
  written qualified. Stitchwort already gets this for free: a namespace's
  names need `import` (`docs/proposals/namespaces.md` D2), and dot notation
  is by type.
- **simp sets**: `@[simp]` is global, `attribute [local simp]` is per
  section, `scoped` per namespace. Stitchwort has no simp set; the nearest is
  which lemmas `rewrite`/`decreasing` look up beside a function
  (`List/Toolkit.sw:1-4`), which `@[internal]` leaves alone.
- **The module system** (Lean 4.22 onward): in a `module` file, declarations
  are private by default, `public` exports one, `public section` changes the
  default, and a public `def`'s *body* isn't unfoldable from other modules
  unless `@[expose]`; `import all M` brings in M's private scope, but only
  within the same package root ([Lean reference, Visibility]). This is the
  Rust-like hard design, and the `import all` escape is the evidence that
  hard privacy needs one in a prover. It also separates *name* visibility
  from *body* visibility, which Stitchwort already has as `opaque`
  (`docs/proposals/opaque-definitions.md`).

### 3.5 Agda: `private` blocks

`private` before a block of declarations keeps them out of the module's
exports; inside the module they're ordinary, and they compute in types, so a
goal can show a private name the user can't write **[remembered]**. Same
problem as 3.1. Agda's `abstract` blocks hide *definitions* (bodies), the
analogue of `opaque`.

### 3.6 Rust: `pub(crate)`

Visibility relative to a boundary (crate, module, `super`), enforced as an
error, and the `private_interfaces` lint warns when a private type appears in
a public signature **[remembered]**. Rust has no goals, so a helper never
leaks by computation. The useful idea is the lint: in std, a public theorem
whose *statement* mentions an internal helper is a smell (§4.4).

### 3.7 `@[internal]`: unlisted, still a name (recommended)

An attribute that marks a declaration as not part of the API. Listings skip
it; nothing else changes.

- (a) yes, (b) yes (the name means what it did), (c) yes (not hashed, not in
  the kernel), (d) yes (on the declaration, in any file), (e) small: an
  attribute in the closed registry (`attributes.rs:79`), one set beside
  `helper_keys`, and the filters at the five listing sites in §1.
- Rules out: a guarantee that users *don't* depend on helpers. A user who
  writes `List.partitionOnto` still can; std's promise is only that it may
  change. Rust and Lean promise more and pay for it with escape hatches.

### 3.8 Local definitions (the existing mechanism)

Move a helper into its owner's body: `def step` inside `List.filter`, named
`List.filter.step` from outside. Already unlisted (§2), already writable.
But it fits only a helper with exactly one owner and no attributes beyond
`tailrec` (`docs/syntax.md:691`); it can't be `opaque` or `{Partial}`
(`docs/syntax.md:360`, `1162`); its captured variables become leading
parameters, changing its signature; and it can't hold a type (`Map.Tree`) or
the dozens of lemmas about `Map.Raw`. Of std's helpers, the `Step`s used by
one function would fit; `partitionOnto`, `reverseOnto` and the `Map`/`Omega`
internals wouldn't. Two mechanisms for one idea isn't worth it, so I'd keep
std's helpers top-level and use 3.7. Local definitions stay the right tool
for a user's own one-off loop.

## 4. The recommendation in detail

### 4.1 The rules

1. `@[internal]` may be written on a definition, a type (data type or
   record), an interface, an ability, and a theorem. Theorems take no
   attributes today (`attributes.rs:33`, "not a theorem"); this adds one.
2. On a type, interface or ability, it covers the whole namespace of that
   name: `@[internal] type Map.Tree` hides `Map.Tree.singleL` and every
   `Map.Tree.*` theorem without marking each. A declaration in that namespace
   can't opt back out (no `@[public]`): if it's API it belongs elsewhere.
3. Internal names **resolve exactly as before**: full name, `import`, dot
   notation. This is what keeps goals readable back: the printer writes a
   call `xs.f` in dot form when `f`'s first explicit parameter has the
   receiver's type (`crates/core/src/pretty.rs:2243-2280`); if dot notation
   skipped internals, the printer (in `core`, which knows nothing of
   attributes) would print goals that don't parse back.
4. `@[internal]` implies `@[noReceiver]`'s exemption from
   `W-RECEIVER-NOT-FIRST`; writing both is redundant (warn, or accept;
   implementation detail, the lane decides).
5. **Listings skip internals** from outside the namespace that declares them:
   completion after a dot and of a bare name, `stitchwort doc NS` and its
   "did you mean", `stitchwort search` unless `--all` (as `%` names now), and
   `doc --coverage`'s count. Asking for one by full name still works:
   `stitchwort doc List.filterStep` shows it, headed "internal: part of std's
   implementation; may change", and so does hover.
6. Not hashed, not in the check cache's fingerprint beyond what the source
   text already is (it's in the text), not in the kernel's declarations
   (D598's rule for attributes).
7. **User programs may use it too**, with the same meaning: an `Aoc.Common`
   helper marked `@[internal]` is listed in its own namespace's files and
   not in the days that import it. One mechanism, nothing std-only to
   explain.

### 4.2 What a user sees in a goal that mentions one

Exactly what they see today, because the goal is the term:

```
⊢ List.filterStep 0 (List.filterStep 1 (List.filter rest p) (p 1)) (p 0) = …
```

Three things change around it:

- **Hover** on `List.filterStep` in the goal shows its doc ("One step of
  `List.filter` …", `List/Toolkit.sw:43`) under the "internal" heading, so
  the user learns where it comes from and that std has lemmas for the public
  function.
- **The std side of the bargain**: for each internal helper that a public
  function's equations expose, std gives lemmas about the public function
  that don't mention it, as `List.filterKeep` and `List.filterSkip` already
  do (`List/Lemmas.sw:349-353`). That's how the user avoids the helper, not
  by being forbidden it. §4.4 makes std check this.
- **Search** still finds lemmas whose statements mention an internal when
  the query names it (`search List.filterStep`): a query naming a
  declaration is asking for it.

A user who writes a lemma about `List.reverseOnto`, as day 20 does, gets no
warning: the name is writable on purpose.

### 4.3 What it costs

- The listing sites in §1 each gain a check; the elaborator keeps a set of
  internal keys (logged like `helper_keys`, `state/tables.rs:10`) and the
  parse-only `Decls` reads the attribute from the AST.
- A sweep of std to mark the helpers (§7) and, where a public function's
  equations expose a helper with no public lemma beside it, the lemma.
- Docs: `docs/syntax.md` "Attributes" table and the language guide's
  attributes section; the std style notes (when to mark).

### 4.4 A std check, like Rust's lint

A std test (not a user warning): no public theorem's statement mentions an
internal declaration, except a list of named exceptions. This keeps std's
promise honest: if users need a fact, it's stated about the public function.
I'd start it as a report in the sweep lane and turn it into a test once the
count is small. (An implementation and sequencing choice; I decided it.)

## 5. How it fits SW-1065 (construction privacy, D2171)

SW-1065 asks for something different in kind: stopping code outside a
namespace from **building** a value that breaks an invariant (a 2025 day 8
`Boxes` that isn't valid). That needs a hard rule, an error at the
constructor, because the point is a guarantee; hiding from completion
guarantees nothing.

They share one idea and should share its implementation: **the owning
namespace**, the boundary inside which a declaration is "at home"
(rule 5's "from outside the namespace that declares them"). SW-1065's design
would reuse that boundary for "who may use this constructor" (Haskell's
export of `T` without `T(..)`; Rust's private fields).

They shouldn't share a keyword: `@[internal]` is a promise about stability
and listings, and is never an error; construction privacy is an error and
interacts with pattern matching, `deriving` and proofs by cases (can a user
match on a `Boxes`?). Keeping them apart means SW-1065 can be designed later
without changing what `@[internal]` means. Std's `Map` already does by hand
what SW-1065 would automate: `Map` wraps a `Quot` of `Map.Raw`, which
carries its own `ordered` and `sized` proofs (`Map/Map.sw:23`,
`Map/Raw.sw:260-264`), so `Map.Raw`'s constructor can't break anything and
only needs to be unlisted.

## 6. How many std declarations it would hide

Counted with grep over `crates/elab/src/std` (4,257 `def`/`theorem`/`type`
declarations, 1,227 of them `def`s); classification by name and doc,
**inferred**, so ±20%.

| Group | Declarations | How marked |
| --- | --- | --- |
| Step and loop helpers of one public function: `List.filterStep`, `partitionStep`, `partitionOnto`, `spanOnto`, `findMapStep`, `maxByStep`, `minByStep`, `mapAccumLeftGo`, `distinctLoop`, `splitStep`, `pushRun`/`buildRuns`/`mergeRuns`/`mapRuns`, `dedupAfter`, `consSome`; `Text.splitCons`, `splitOnLoop`, `wordsStep`, `wordsClose`; `Nat.divStep`, `Nat.digitsOnto`; `Parse.chainStep`, `manyStep`, `sepStep`; `Result.traverseLoop`, `Vec.traverseOptionLoop`; `Map.lookupWithOnto`, `Map.liftBinary` | about 35 defs | one by one |
| `Map.Tree` (the balanced tree) | 119 (39 defs) | `@[internal] type Map.Tree` |
| `Map.Raw` (tree plus invariants) | 129 (40 defs) | `@[internal] type Map.Raw` |
| `Omega` (the `omega` tactic's syntax and soundness) | 112 (51 defs) | its types, and the rest one by one |
| `Ring` (the `ring` tactic's syntax and soundness) | 83 (32 defs) | the same |
| **Total** | **about 480, of which about 195 defs and types** | |

About 11% of std's declarations and 16% of its definitions; the theorems
are almost all in the four internal namespaces.

**Left public on purpose:** `List.reverseOnto`, `lengthOnto`,
`withIndexFrom`, `findIndexFrom` and the like, the "from an accumulator"
generalisations that users prove things about because induction needs them
(day 20; `withIndexFrom` in 6 app files); and `Map.Spec`, the list model
that `Map`'s proofs are stated in, which three 2024 days use. These are the
judgement calls; D2891 asks about the principle.

## 7. Questions for Matt

- **D2890:** Hide std's helpers with an `@[internal]` attribute that only
  takes them out of completion, `doc` and `search`, leaving every name
  writable and goals unchanged, rather than a `private` that makes them
  unwritable outside std? [rec: yes, because helpers appear in goals and
  users already write lemmas about them (day 20's `reverseOnto`, the 2024
  `sameKey` rewrites); a hard rule would break those or need an escape hatch]
- **D2891:** Is the line "internal = a user never needs to write it, even in
  a proof", so accumulator forms such as `List.reverseOnto` and
  `List.withIndexFrom` stay public API (with docs and stability)? [rec: yes,
  because users' induction proofs need them, and hiding a name people must
  write only makes them harder to find]
- **D2892:** May user programs use `@[internal]` too (an `Aoc.Common`
  helper hidden from the days that import it)? [rec: yes, because it's the
  same mechanism at no extra cost, and AoC's shared logic has the same
  helpers]
- **D2893:** Keep construction privacy (SW-1065) a separate, enforced
  feature that reuses `@[internal]`'s "owning namespace" boundary but not its
  keyword? [rec: yes, because one is a listing hint and the other a
  guarantee, and mixing them would make `@[internal]` an error somewhere]

Decided here, as implementation details: a type's `@[internal]` covers its
namespace with no opt-out; dot notation still resolves internals (so goals
read back); `@[internal]` implies `noReceiver`'s exemption; the std check of
§4.4 starts as a report.

## 8. Tickets to file

In order; 1 before 2, 3 after 2.

1. **`@[internal]`: the attribute and the listings** (Sonnet, 75 min). Add
   it to the registry (`attributes.rs`) for definitions, types, interfaces,
   abilities and theorems; an `internal` key set beside `helper_keys`,
   covering a marked type's namespace; filter it in `dot.rs` (members after
   a dot), `nav.rs` (`names_in_scope`), `driver/src/search.rs` (`hidden`,
   `--all` shows them), `driver/src/doc.rs` (`members_of`, `closest`,
   the "internal" heading) and `doc/coverage.rs`; imply the
   `W-RECEIVER-NOT-FIRST` exemption. Docs: `docs/syntax.md` attributes
   table, the guide's attributes page. Tests: new `examples/accept/internal.sw`
   (still resolves by full name, import and dot; a lemma about one checks),
   `task test:one -- receiver_first`, `-- doc`, `-- search` (the
   `crates/cli/tests/server/search.rs` and `tools/doc.rs` cases), and an
   LSP completion test that an internal is missing after `xs.`. Near the
   elaborator but no kernel terms: Sonnet.
2. **Mark std's internals** (Sonnet, 60 min). Mark the groups in §6 (about
   35 helpers one by one; `Map.Tree`, `Map.Raw`, and the `Omega` and `Ring`
   types); drop the now-redundant `@[noReceiver]` on them. Report the public
   theorems whose statements mention an internal (§4.4). Since the attribute
   isn't hashed this shouldn't move hashes, but it edits std core files, so
   it runs `task snap:hashes` and the `hash_stability` test, and extract's
   `bound_to_the_prelude` tests (native pins). Absorbs the S12 part of the
   std review's follow-ups.
3. **Public lemmas instead of helpers** (Sonnet, 45-90 min, from ticket 2's
   report). For each public theorem or equation that only states a fact via
   a helper, add the lemma about the public function (as `filterKeep`/
   `filterSkip`), then turn the report into a std test with a short
   exception list. Tests: the new lemmas' files with `task test:one`, and
   `task audit:touched -- List` (and the other namespaces touched).
4. SW-1065 (construction privacy) stays in backlog; its note should cite §5.

## Sources

- [Lean reference, Visibility] Lean Language Reference, "The Module System:
  Visibility", <https://lean-lang.org/doc/reference/latest/The-Module-System/Visibility>
  and the 4.22 and 4.23 versions of the same page (fetched by search, 7
  November 2026): private by default in a `module`, `public`, `public
  section`, `@[expose]`, `import all` within the same root.
- Everything marked **[remembered]** is from memory, not checked this
  session.

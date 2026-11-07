# Proposal: the compiler's references to std, checked (SW-1392)

Design note only, 7 Nov 2026. Nothing here is built. Read-only survey of
`crates/` at `cd67c1111`. Line numbers are at that commit.

## 0. Summary

**What users get.** Stitchwort writes proofs for you: `omega`, `ring`,
`deriving`, the equation lemmas `f.eq.N`, `decreasing`, `auto`. The Rust
code builds those proofs from std lemmas that it names in strings
(`"Std.Bool.orLeft"`), and it gives their arguments by position. Today a std
rename, or a change to which of a lemma's arguments are implicit, can make
one of these features stop working with no error at build time. Sometimes
nothing fails at test time either: `auto` quietly stops using `omega`, an
`f.eq.2` is no longer generated, a nested-induction lemma isn't derived. With
this change, every such reference is in one table. A std edit that renames a
referenced declaration, or changes the shape of its arguments, stops the
library from loading, with an `E-BUILTIN` error that names the declaration
and shows the old and new shape. That failure comes on the first test run of
any kind, before any proof is built.

**Recommendation.** Put every Rust reference to a std declaration in the
existing built-in registry (`crates/core/src/registry.rs`). Each entry the Rust
code applies to arguments also records its **argument shape**: which binders,
which implicit, in what order. That shape is checked when the declaration is
bound, while the library loads (design A). On top of that, add one generated
snapshot of the full statements of those entries, plus a source scan that
fails if a new string reference to std appears outside the table (design C).
A helper that builds calls by binder name (design B) is not worth a rewrite of
the proof generators now. Once A is in, positions are checked at load, so B
would only make the code easier to read.

**For the naming sweep (SW-2179) until this lands:** one grep per renamed
name and four targeted tests, in §5. One fix should go in before the sweep:
the congruence audit silently skips a `…Cong` lemma whose function was
renamed (§3.4).

## 1. The problem

### 1.1 Two concrete breaks

*A rename.* Suppose the sweep renames `Bool.orLeft` to `Bool.orIntroLeft` in
std. `omega` looks it up by the string `"Std.Bool.orLeft"`
(`crates/elab/src/omega.rs:649`, and again in its `LIBRARY` list at `:132`). Here is what happens next:

- When `omega` is written out, the build passes. The first `omega` in a test
  then fails with `E-OMEGA-INTERNAL`: "`Std.Bool.orLeft` isn't available (the
  library file that declares it isn't loaded)" (`omega.rs:620-626`). That
  message is loud, but it's misleading.
- `omega` also runs when nobody writes it: when `cases` closes an arithmetic
  case (`prove_case`, `omega.rs:315-317`), when `rewrite` discharges a premise
  (`prove_premise`, `omega.rs:244`, `275-277`), and inside `auto`
  (`prove_for_auto`). There the same lookup failure turns into `Ok(None)`, and
  the feature just stops. A user sees "`auto` couldn't prove `x + 1 ≠ 0`"
  where it used to work.
- If the renamed name is `Std.Omega.prove` itself, `needs_reach_omega`
  (`crates/elab/src/library.rs:1106-1120`) finds no owner for it. It answers
  `false`, and `auto` stops trying `omega` in every module, with no message
  anywhere.

*A binder change.* SW-1381 made lemmas take arguments that their hypotheses
fix as implicit (`[x: a]`). `omega` builds `Bool.orLeft`'s calls by hand, so
its code had to change to match: `or_intro` now hard-codes the two sides as
implicit (`omega.rs:4056-4061`). Any lemma that the compiler builds a call to,
and that nobody remembers to update, gets a term the kernel refuses. The
kernel requires an application's implicitness to match its Pi
(`crates/core/src/check.rs:318-321`), and it reports "this isn't a function"
at the user's own theorem. `deriving Finite` is exposed the same way. It
applies `List.memAppendLeft` to four explicit arguments
(`crates/elab/src/derive_finite.rs:503-511`), but std declares it as
`theorem List.memAppendLeft (x: a): (xs: List a) → …`
(`crates/elab/src/std/core/Finite.sw:10`). `x` is exactly the kind of
parameter SW-1381's rule makes implicit. If it were, every `deriving Finite`
would fail with a type error pointing at the user's `deriving` clause.

In SW-1381 itself, the one break that got through was in `decreasing` under
`Option.map` (`Option.mapCong` made implicit). Review caught it, not a test.
SW-1395 then added `every_std_congruence_lemma_passes_validate_cong`.

### 1.2 Why it will happen more

The sweep (SW-2179) will rename operations and lemmas across std. The
SW-2159 lanes are adding about 75 lemmas. Some of them will be put in the
bracket style and renamed in the same pass. A rename lane today has no list
of which names the compiler depends on.

## 2. Inventory

I found seven ways the Rust code refers to std. The counts are of
non-test source in `crates/*/src`, by grep. The counts marked "about" include
a few literals I classified by reading the line.

| # | Mechanism | Where | Count | Resolved by |
|---|---|---|---|---|
| M1 | Registry built-ins (`Builtin::X`) | 70 files, 1,035 uses | 251 entries: 182 defs, 34 data, 35 ctors; 77 in library files | name, at prelude load (`registry.rs:712-753`) |
| M2 | Name string → id, then a kernel term built by position | omega 95 (51 defs, 44 ctors) + 8 range lemmas; ring 23; equations 21; equations/induct 2; derive_induct 9; auto 4; interfaces 5; membership 1 | **about 168** | `cx.e.named`, `lookup_def`, `scope.get` at use |
| M3 | Surface syntax naming std, then elaborated | derive_ord 35, derive_finite 18, derive 14, derive_show 6, derive_decide 3, parser 9 + sections 2, membership 3, module 2, check 1 | about 93 literals, about 60 distinct names | ordinary name resolution of the generated `Expr::Var` |
| M4 | A declaration recognised by comparing its path text | pretty 6, tailrec 16, lib.rs 7, cases 2, ring 1, search/search_at/doc 3 (`Std.Iff`), counterexample 2, check 1, js 1 | about 39 | `def.path() == "Std.…"` |
| M5 | Lists of names whose files must load | omega `LIBRARY` 41 (`omega.rs:119-162`), ring `LIBRARY` 6, `GUARD_LEMMAS` 13, `MEMBERSHIP` 2, `RANGE` 1 | 63 | library index |
| M6 | Names written into messages and hints | closing 2, search_at 1, matching 2, redundant 2 | 7 | `write_name` or text |
| M7 | Naming conventions | congruence `{f}Cong` and `SUFFIXES`; equations `{key}.unfold` | 2 rules | `format!` + `scope.get` |

In all, about **370** references to std by text outside the registry, plus
the registry's 251.

### 2.1 What each one does today when a name or its binders change

| # | Std rename | Binder change (order, count, implicitness) | Depends on positions? |
|---|---|---|---|
| M1 core entry | **Loud at every load**: `E-BUILTIN` "the prelude doesn't declare what the compiler needs" (`registry.rs:756-778`), so every test fails | Not checked, except the 23 content-hash pins (`crates/core/src/pins.rs:78-175`), `nat_add.rs:241-259` (the types of `Nat.addZero` and `Nat.addSucc`), and the natives' shape checks in `native.rs`. Otherwise a wrong term the kernel refuses, or a silent skip (below) | Yes, wherever the term is built by hand: `decreasing/plain.rs:622-639` hard-codes `Decidable.elimIf`'s 9 arguments and their implicitness; `partial.rs` hard-codes the arity of each `Effect` primitive |
| M1 library entry | **Loud in one test**: `the_prelude_binds_every_builtin_to_a_final_declaration` (`crates/driver/tests/library/builtins.rs:19-47`) runs `check_complete`. Elsewhere it is bound only when its file loads | as above | as above |
| M2 omega/ring | Explicit `omega`/`ring`: loud but misleading (`E-OMEGA-INTERNAL`, "isn't loaded"). Inside `cases`/`rewrite`/`auto`: **silent**, the feature stops | `lemma()` (`omega.rs:918-933`) reads implicitness off the type, so a flip in place is tolerated, but a reorder or a count change gives a wrong term. `or_intro` and `apps` hard-code implicitness. The pre-check (`omega.rs:3993-4050`) catches some cases as `E-OMEGA-INTERNAL`; the rest reach the kernel | Yes |
| M2 equations | `Decidable.elimEq` and `Bool.trueNotFalse`: `Stop::Skip("the core's logic isn't loaded yet")` (`equations.rs:4481-4501`). The other 19 are `Option`s, so the feature turns off. **Silent until a user writes `f.eq.N`**, when they get the misleading reason | `elim_eq` checks only the binder count and skips on a mismatch (`equations.rs:1496-1497`): **silent** | Yes |
| M2 derive_induct | `nested_lib()` returns `None` (`derive_induct.rs:317-345`) and the nested lemmas are **silently not derived** (`:283-285`) | Every argument explicit by position (`:1603-1634`), so the kernel refuses the generated lemma | Yes |
| M2 auto | `FACT_LEMMAS` (`auto.rs:392`) names `Nat.nonzeroOfSuccLe` with **"2 arguments before the premise"**. A rename gives `Ok(None)` (`:442-444`): **silent** | A changed count gives a wrong premise and the lemma never fits: **silent** | Yes (an arity in the table) |
| M3 derive, parser | **Loud at the use**: `E-UNKNOWN-NAME` at the user's `deriving` clause or operator | The elaborator inserts implicits, so only explicit arguments are positional. A changed explicit argument gives a type error at the user's clause, loud but misattributed | Explicit arguments only |
| M4 recognition | **Silent**: the printer stops showing `a ..< b` (`pretty.rs:1299`), tail-recursion analysis stops seeing effect blocks (`tailrec.rs:621-654`), `ring` stops treating `Nat.pow` specially (`ring.rs:960`) | Some read arguments by position (`tailrec.rs:623`'s `[.., computation, next]`) | Some |
| M5 load lists | **Silent**: the file isn't loaded, and the feature finds its names missing (as M2) | n/a | No |
| M6 messages | **Silent**: a hint names a declaration that doesn't exist | n/a | No |
| M7 conventions | **Silent**: renaming `f` but not `fCong` turns off `decreasing` and `rewrite` under `f`, and the audit skips it (§3.4) | `validate_cong` checks it, and SW-1395's test runs that on every `…Cong` | n/a |

The silent column is the problem. Every **Silent** entry in that table is a
feature that switches itself off. Confidence: I read the code paths quoted
here. I did not run anything, so "silent" means no error is raised on the path
I read. Some example's snapshot may still change and catch it.

## 3. What already catches a break

1. **Registry completeness.** `check_complete_core` runs at every prelude load
   (`crates/elab/src/lib.rs:866`). `check_complete` runs over all entries in
   one test (`builtins.rs:29`). These catch renames, but only of the 251
   registry entries, and nothing about their binders.
2. **Pins (SW-2081).** 23 kernel natives are pinned by content hash, and each
   pin is checked where its built-in is bound (`every_pin_is_checked_at_binding`,
   `crates/driver/tests/library/pinned_hashes.rs`). A content hash covers the
   type, so these 23 are fully protected, binders included. The JS and runtime
   natives aren't pinned yet (SW-1991, which closes SW-1586).
   `*_bound_to_the_prelude` (`crates/cli/tests/extraction/extract.rs:3211-3290`)
   covers JS's text, Int and Nat bindings by hash, but only when someone runs
   it.
3. **The hash snapshots.** `library__hash_stability__prelude.snap` and
   `the_library_hashes_as_in_the_release_build` change on every std edit, so a
   rename lane accepts them as a matter of course. They say *that* something
   changed, not that the compiler depends on it.
4. **`every_std_congruence_lemma_passes_validate_cong`** (SW-1395,
   `pinned_hashes.rs:225`). This is the nearest thing to what this note wants:
   it loads the whole library and checks every `…Cong` lemma's shape. It has a
   hole, though. When the function a lemma is named after can't be found, it
   `continue`s (`crates/elab/src/congruence.rs:702`). So a lemma orphaned by
   a rename is skipped, and that is exactly the case the sweep creates.
5. **The kernel.** A wrong generated term is refused. But it is refused at
   the user's declaration, with a message about their code, and only on the
   paths some example exercises.
6. **Examples.** Every omega, ring, derive and decreasing example breaks on a
   rename that reaches an explicit use. None covers the silent paths in §2.1,
   because a silent path doesn't change the output of an example that still
   proves its goal another way.

## 4. Designs

### A. Every reference in the registry, with its argument shape checked at load

**The change.** Every std declaration that Rust code names becomes a
`Builtin` entry. Library ones get `Home::Library`, as `Int.tdiv` and `Array`
already have. For each entry that Rust applies to arguments, the `builtins!`
row also gets a shape:

```rust
ElimDecEq = "Decidable.elimEq": Def ["[p] [a] d y n z yesEq noEq"],
MemAppendLeft = "List.memAppendLeft": Def ["[a] x xs ys _"],
OmegaNv = "Omega.NTerm.NV": Ctor(OmegaNTerm) [1],
```

Each word is one leading Pi of the stored type, read without unfolding: `[x]`
is implicit, `x` explicit, `_` an anonymous binder. A constructor's shape is
its number of fields. `bind_def` and `bind_data` compare the shape when they
bind, as the pins are checked there now (`pins::check_bound_def`). A
mismatch refuses the library:

> E-BUILTIN: the library's `Decidable.elimEq` doesn't have the arguments the
> compiler builds it with: expected `[p] [a] d y n z yesEq noEq`, found
> `[p] [a] (d) [y] …`

Two more checks finish it off:

- **Library entries fail at startup, not on first use.** When the library
  index is installed, every `Home::Library` entry must have an owner in it.
  `index.owner` already exists (`library.rs:1116`). A rename then fails every
  session, the way a core rename does now. It is one map lookup per entry.
- **"Not loaded" and "missing" become different things.** `Lib::new` for omega
  and ring uses `loaded_def` and `loaded_ctor`. `None` then means "this module
  doesn't load omega's file", and that stays a quiet `None`. "Loaded but
  missing" can't happen any more, because of the startup check.

The other mechanisms move onto the table too:

- **M2** sites call `builtin_def`, `loaded_def` or `loaded_ctor`.
- **M3** generators build `Expr::Var` from `Builtin::X.name()`, through a
  small `s.std(Builtin::X)`.
- **M4** comparisons become `registry.is_def(Builtin::X, id)`.
- **M5** lists are built from `Builtin` names.
- **M6** messages print `Builtin::X.name()`.

The parser can't see the registry (`stitchwort-syntax` sits below core). Its
nine names become one exported list, and a core test checks that each is a
registry name.

**What it should do.** Renaming `Bool.orLeft` in std fails every test run
with one `E-BUILTIN` line naming it. Making `List.memAppendLeft`'s `x` implicit
fails the same way, with the old and new shape side by side. The fix is to
change the registry row and then the code that `Builtin::MemAppendLeft` points
to, which `grep` finds because it is now an identifier. Rust code can't
misspell a std name, because the compiler checks the enum variant.

**Cost.** About 250 new rows, of which roughly 170 need a shape. The
`unbound` search in `registry.rs:746` is linear over all entries for every
declaration bound. Doubling the table doubles that, so it should become a
`HashMap` by name in the same stage (my call). Library entries must keep to
`loaded_*` outside the code that loads them, or the debug assertion at
`registry.rs:626` fires; SW-1711 was that bug.

**What it rules out.** Rust code reaching a std declaration by text. That is
the point. It doesn't catch a statement that changes while its binders stay
the same (`a ≤ b + a` becoming `a ≤ a + b`). For that, see C.

**Elsewhere.** GHC's `GHC.Builtin.Names` is this design: every library
entity the compiler means is a "known-key name" in one table, and a missing
one is an error when the module loads. rustc's lang items go one step
further, with an attribute on the library item, so renaming the item is free
(design D).

### B. A call builder by binder name

**The change.** `Call::of(g, Builtin::ElimDecEq).arg("d", d).arg("z", z)
.implicit("p", p)….build()?` walks the lemma's Pi telescope, places each
argument by binder name, and takes each one's implicitness from the type. It
errors if a name is unknown or a binder is left unfilled.

**What it should do.** Reordering a lemma's binders, or flipping their
implicitness, wouldn't break any caller. Renaming a binder fails at the first
call, in a test.

**Cost.** It means rewriting about 300 call constructions in the most
delicate code we have (omega's 4,000 lines, equations, derive_induct,
decreasing), all of it code that generates kernel terms, so each change is a
proof-generation change that needs Opus review (D2364). The checks happen at
use, so a path no test reaches is still unchecked. It doesn't catch renames
of the lemma at all.

**Elsewhere.** Lean's `mkAppM` infers implicit arguments by unification, and
it fails loudly on a mismatch. Lean meta code names constants as
``` ``Nat.add_comm ```, which is checked when the meta code is compiled. That
check is the design A half.

### C. A generated test over every referenced name

**The change.** One test loads the whole library, the same setup as SW-1395's
test, so a few seconds. For every registry def it prints the full statement
(`Decidable.elimEq: [p: Prop] → [a: Type] → (d: Decidable p) → … →
Decidable.elim d y n = z`) into an insta snapshot. A second, grep-style
test, like `pinned_hashes.rs`'s "no 64-digit hex literal hides from it",
scans `crates/*/src` for string literals of the form `"Std.X.y"` and
`"X.y"` that name a declaration, outside `registry.rs` and an allowlist. That
keeps the table complete.

**What it should do.** Any change to a referenced statement, even one that
keeps its binders, shows as a snapshot diff in the lane that made it. The
reviewer then knows that compiler code depends on that statement. The scan
stops new string references from creeping back in.

**Cost.** Small: two tests. On its own, without A, it fails only at test time,
and the fix is "accept the snapshot", which a lane can do without reading the
Rust code. That is why it comes after A, not instead of it.

### D. (Considered) A lang-item attribute in std

Mark the std declaration instead: `@[compiler elimEq]` (attributes exist,
`docs/proposals/attributes.md`), and Rust looks up by key. Renames become
free, and a std author can see that the compiler depends on a declaration.
But it is a language change. It touches hashing and the check cache (an
attribute is part of a declaration's identity or it isn't). It doesn't help
with binder changes, and nothing needs renames to be free: the goal is that
they fail loudly. Not now (D3180).

### Comparison

| | Rename | Binder change | Statement change | Fails | Cost |
|---|---|---|---|---|---|
| A | load, every run | load, every run | kernel, on use | before any proof | ~250 rows, 4 lanes |
| B | no | tolerated or at use | kernel, on use | in a test that reaches it | ~300 call sites in kernel-term code |
| C | test | test | **test** | one test | 2 tests |
| D | free | no | no | n/a | language change |

**Recommended: A, then C.** A turns every silent case in §2.1 into a load
error, checks the one thing the Rust code depends on (argument positions),
and builds on two mechanisms we already trust: the registry and the
check-at-binding of the pins. C covers what A can't (statements) for the
price of a snapshot, and its scan stops the table from drifting. B adds
nothing that A doesn't already catch. If the hand-built calls in
`decreasing/plain.rs` or `omega.rs` ever get too hard to read, it can come
back as a refactor.

## 5. What the naming sweep does until this lands

Every rename or binder change of a std declaration, in SW-2179's lanes and in
SW-2159's moves, does this before committing:

```sh
# for each renamed or re-bracketed declaration, written without `Std.`
old='Bool.orLeft'
rg -n --glob '*.rs' -F -e "\"Std.$old\"" -e "\"$old\"" crates
# for a renamed namespace (`Ord` → …), also the prefix uses (pretty.rs, js):
rg -n --glob '*.rs' -F "\"Std.${old%%.*}." crates
```

A hit means you either update the Rust site in the same lane, or keep the old
name. The registry's rows are unprefixed (`"Bool.orLeft"`), and so is
equations' `def("Decidable.elimEq")`, so both patterns are needed. The grep
won't find the M7 conventions: **rename `f` together with `fCong`,
`fCongMem`, `fCongRange` and `fCongRangeFrom`**, or `decreasing` and
`rewrite` stop working under `f`.

Then run four targeted tests, about a minute in all:

```sh
nix develop -c task test:one -- the_prelude_binds_every_builtin \
  every_std_congruence_lemma_passes_validate_cong every_pin_is_checked_at_binding \
  bound_to_the_prelude
```

If the grep hit omega, ring, deriving, equations or decreasing, also run that
feature's examples, for example
`nix develop -c task test:lane AREA=examples NAME=omega,ring,derive,decreasing`
(pick the names that apply).

## 6. Calls I made

- **The registry is the table**, not a new `StdRef` enum in `elab`. It
  already binds by name at load, already has `Home::Library`, already holds
  `Decidable.elimEq` and the other lemmas `decreasing` uses, and its doc
  already counts `deriving` and `calc` among its users (`registry.rs:49-56`).
- **A shape is a syntactic Pi prefix with binder names**, not a full expected
  type written in Rust (the `nat_add.rs` style). Writing 170 expected types
  out by hand would duplicate std. Names are included so that B stays
  possible and the error message is readable. `_` matches an anonymous
  binder.
- **A shape mismatch refuses the library** (`E-BUILTIN`), the same as a stale
  pin, and not a warning. Std ships with the compiler, so a mismatch is always
  our bug (D2543: limits fail, never choose).
- **The equations `skip` on a shape mismatch** (`equations.rs:1496`) becomes an
  internal error once A checks shapes at load.
- **Sequencing**: the congruence-audit fix and the §5 check first. Then A in
  three lanes, then C. Sweep lanes that rename names the compiler references
  wait for A's stages 1-3. The others go ahead with the §5 check.

## 7. Questions for Matt

- **D3180:** Should std mark the declarations the compiler depends on, for
  example with an attribute like `@[compiler]`, so a std author sees it in the
  source (design D)? [rec: not now, because the registry plus a load-time
  error tells the author at once, and it can be revisited if outside
  contributors start editing std.]

## Tickets to file

In order. Model per CLAUDE.md: this is work near the kernel and proof
generation, so it goes to Sonnet. Stages that move kernel-term generators get
an Opus review (D2364).

1. **[Sonnet] Congruence audit: an orphaned `…Cong` lemma fails.**
   `std_congruence_failures` reports a `…Cong` whose base function isn't found,
   instead of `continue` (`congruence.rs:702`). Do this before the sweep. 20
   min. Tests: `task test:one -- every_std_congruence_lemma_passes_validate_cong`.
2. **[Sonnet] Registry shapes and the startup check (A, stage 1).** Add the
   shape column to `builtins!`, check it in `bind_def`/`bind_data`, and
   replace `unbound`'s linear search with a map. Check that every
   `Home::Library` entry has an index owner when the library installs. Give
   shapes to the existing entries that Rust applies to arguments
   (`ElimDec*`, `IfCong`, `EqSym`, `EqTrans`, `VoidExfalso`, `FalseNotTrue`,
   `BoolUniqueEq`, the Effect primitives and so on). Add a unit test that a
   wrong shape is refused. 60 min. Tests: `task test:lane AREA=core`,
   `task test:one -- the_prelude_binds_every_builtin every_pin_is_checked_at_binding`.
3. **[Sonnet] omega and ring through the registry (A, stage 2).** Move the
   string names in `Lib::new` (`omega.rs:619-760`, `Ranges::new`,
   `ring.rs:465-500`) to `Home::Library` entries with shapes, use
   `loaded_def`/`loaded_ctor`, and build `LIBRARY` from them. Opus review
   (kernel terms). 75 min. Tests: `task test:lane AREA=examples NAME=omega,ring`,
   `task test:one -- the_prelude_binds_every_builtin
   a_nested_library_load_keeps_the_outer_units_omega_for_auto`.
4. **[Sonnet] The other proof generators through the registry (A, stage 3).**
   `equations.rs` `branch_lib`, `equations/induct.rs`, `derive_induct.rs`
   `nested_lib`, `auto.rs` `FACT_LEMMAS` (the arity comes from the shape),
   `interfaces.rs`, `membership.rs`, `GUARD_LEMMAS`, and `decreasing/plain.rs`'s
   hard-coded arguments checked against shapes. Opus review. 75 min. Tests:
   `task test:lane AREA=examples NAME=equation,induct,decreasing,auto,guard`,
   plus the equations unit tests it touches by name.
5. **[DeepSeek] Syntax generators, recognisers and messages through the
   registry (A, stage 4).** Mechanical. M3: `derive*.rs`, membership, module,
   check, with the parser's names as one exported list plus a core test that
   each is a registry name. M4: pretty, tailrec, lib.rs, cases, ring's
   `Nat.pow`, search/search_at/doc's `Std.Iff`, counterexample, js. M6:
   closing, search_at, matching, redundant. 60 min. Tests:
   `task test:lane AREA=examples NAME=derive`, `task test:lane AREA=syntax`,
   the pretty and tailrec unit tests by name.
6. **[Sonnet] Statement snapshot and source scan (C).** Add
   `std_references_keep_their_statements` (an insta snapshot of every
   registry def's printed type) and `no_std_name_outside_the_registry` (a scan
   of `crates/*/src` with an allowlist for namespace logic such as
   `starts_with("Std.")`). Add a note in `docs/workflow.md`: a diff in this
   snapshot means "check the Rust users of that entry". 45 min. Tests: the two
   new tests.

Related: SW-1991 (closes SW-1586) stays separate. Pins protect what a
*native* means. Shapes protect where the *Rust code* puts arguments. A pinned
entry's hash already implies its shape. SW-2179's lane plan should cite §5.

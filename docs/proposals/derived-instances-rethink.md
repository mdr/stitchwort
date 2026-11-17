# Derived instances' cost, thought through again (SW-3725)

**Status:** proposed, 17 November 2026. A paper lane: nothing in the tree
changed. Follows [derived-instances-import-cost.md](derived-instances-import-cost.md)
(SW-3710), which measured the problem and proposed options A to D; this note
asks why the cost exists and what the end state should be. Migration cost
is not counted (D2303).

How claims are marked: **[measured]** run today (the release CLI built from
`0d09b858a`, `check --no-cache`, `STITCHWORT_TIMINGS=decls`, Speedwell at
load 4 to 6, one run each unless said; steps are exact, milliseconds rough);
**[checked]** read in the code at the place given; **[cited]** from a page
fetched today, link given; **[inferred]** reasoning, not run;
**[estimated]** a number I expect, with the reasoning. The probes are small
generators (`gen.py`, `gen2.py`, `gen3.py`, `gen4.py`) in the lane's
scratchpad, reproduced in the appendix so they can be rerun.

## 1. In plain words

**The problem.** Since every type gets `==`, `<`, printing and `Finite`
automatically (D3609), a cold start that imports std costs 0.6 to 1.1 s more.
SW-3710 put that down to the generated law proofs costing "about 50K steps
per constructor per proof". That figure is true for a constructor with two
fields, but it hides the real shape of the cost, which is this:

- **The cost grows with the cube of the number of fields in a
  constructor**, not with the number of constructors. A record with 4
  fields costs 0.28M steps to declare, with 8 fields 2.0M, with 16 fields
  19M (1.6 s), and with 32 fields 233M (**30 s**) [measured]. Sixteen
  constructors of two fields cost 2.3M.
- So the bigger problem is not std's import. It is that a user's wide
  record (a game's state, a parser's configuration) has a cliff waiting for
  it. Today's widest records in `aoc/`, `games/rogue` and `tools/` have 9 to
  11 fields [checked, by a rough search], so nobody has hit it yet.
- The cube is not inherent. It comes from how the proofs are written and
  from a slow path in the elaborator that the generated source happens to
  hit. The same proof idea written another way is 12 to 26 times cheaper at
  16 to 32 fields [measured on a prototype of the `==` half, §3.4].
- Separately, **a warm check cache makes the whole import cost vanish**: the
  Nat program is 1.95 s cold and 0.34 s with std's entries cached, against
  0.28 s with no import at all [measured]. That beats every option that
  changes what is derived, and it also removes the 1.1 s that importing std
  cost before D3609.

**The options**, in the order I would rank them:

| Option | What | Saves | Trust | Build (agent time) |
|---|---|---|---|---|
| C | Make the generated proofs cheap: fix the elaborator's slow path, reshape the proofs, guard with a step budget | Removes the cliff for users' types; std's extra roughly halves [estimated] | None | Opus, about 3.5 h in two lanes |
| D | One check cache for std per machine (and shipped with releases), not one per project | Cold start 1.95 s → about 0.35 s after the first run on a machine [measured warm] | None new: same entries, another folder | Sonnet, about 1 h; shipping later |
| B | Don't derive for std's 14 internal types | 9.0M of Nat's 9.5M extra steps [measured, SW-3710] | None | Sonnet, under 1 h |
| A | Derive std's instances on first use | As B, for types nobody compares | None, but what exists depends on what a program uses | Opus, 2 h plus a design |
| F | Check proofs later or on other cores | Wall-clock only | None if the verdict waits | Large; architecture |
| G | One generic theorem over a description of the type | Unknown; likely worse | None | Opus, 8 h or more, risky |
| K | A kernel rule for structural equality | At most the kernel's 19% plus elaboration | The kernel grows | Not recommended |

**Recommendation.** Do C and D, and neither A nor B.

- C, because the cliff is a defect whatever happens to std: D3609's promise
  that automatic derivation is cheap is false for wide types today, and the
  fix helps every program. SW-3719 is the ticket; this note gives it
  concrete targets (§3) instead of "no single hotspot".
- D, because it is the only option that removes the import cost itself, and
  it is small: entries are already keyed by content and compiler, only the
  folder is per project.
- Not A: it makes which declarations exist depend on what the program
  uses, in the middle of another definition's elaboration, to save a cost
  that C shrinks and D removes. Lean and Isabelle both went the other way:
  cheaper eager constructions, not lazy ones (§5).
- Not B as syntax. With C and D in, internal types cost little and nothing
  at start-up, and "every type has them" stays true without a list of
  exceptions. If the 0.6 s matters this week, a temporary skip of
  `Std.Omega.*` and `Std.Ring.*` inside the compiler (no syntax, removed
  when C lands) is a 30-minute stopgap.

Two questions for Matt are at the end (§7).

## 2. What is generated, and where the cube comes from

### 2.1 The shape of one proof [checked]

`eq_source` (`crates/elab/src/derive.rs:1617`) writes, per constructor
`C a0 … a(f-1)` of a type with two or more constructors:

```text
T.%sameSound (C a0 a1) s h =
  let e : T.%tag s = c := Eq.flipped (DecEq.tagsSame c (T.%tag s) h)
  let b0 := T.%C%0%at s e;  let b1 := T.%C%1%at s e
  let v : (DecEq.decide a0 b0).holds && (DecEq.decide a1 b1).holds = True :=
    J (y q => T.%same (C a0 a1) y = True) h (Eq.flipped (T.%etaAt s c e))
  Eq.trans (Decidable.sound WHOLE v) (T.%etaAt s c e)

WHOLE = (Decidable.map
           (Decidable.andThen (DecEq.decide a0 b0) (u => DecEq.decide a1 b1))
           (q => J (y _ => C a0 a1 = C b0 y)
                   (J (y _ => C a0 a1 = C y a1) byComputing (And.left q))
                   (And.right q))
           (e => And.Both (Eq.cong (T.%C%0 a0) e) (Eq.cong (T.%C%1 a1) e))
         : Decidable (C a0 a1 = C b0 b1))
```

`%sameComplete` states `WHOLE` again (for `a` against `a`), and the order's
`%equal` builds the same congruence a third time (`fields_equal`,
`derive.rs:2162`, is shared as Rust code, not as a lemma). The order's
`%flip` and `%trans` chain one core lemma per field (`Ordering.thenFlip`,
`Ord.thenTrans`; `derive_ord.rs`).

Three things in this shape nest to the right, one level per field:
`Decidable.andThen`, `And.Both`, and the hypothesis `q`, a conjunction
`a0 = b0 ∧ (a1 = b1 ∧ …)` from which field `k`'s equation is read as
`And.left (And.right (… (And.right q)))`, `k` levels deep. At each level the
implicit arguments are the whole remaining tail.

### 2.2 The cube, measured

**By fields, eight constructors** (`type T = | TK0 (f0: Nat) … | …`):

| Fields per constructor | Steps | Per constructor | Nodes | Elab + kernel ms |
|---|---|---|---|---|
| 0 | 77K | 9.6K | 2.1K | 8 |
| 1 | 426K | 53K | 9.2K | 37 |
| 2 | 1.14M | 143K | 15.5K | 79 |
| 3 | 2.83M | 353K | 26.0K | 182 |
| 4 | 6.09M | 761K | 41.4K | 371 |

**By fields, one constructor** (a record):

| Fields | Steps | Nodes | Elab ms | Kernel ms |
|---|---|---|---|---|
| 2 | 61K | 1.3K | 5 | 1 |
| 4 | 278K | 4.3K | 17 | 3 |
| 8 | 1.97M | 21.5K | 127 | 11 |
| 12 | 7.24M | 61.7K | 527 | 30 |
| 16 | 19.3M | 135K | 1,597 | 66 |
| 32 | 233M | 953K | 29,995 | 494 |

Doubling the fields multiplies the steps by 7 to 12: cubic, drifting
towards the fourth power. The terms produced grow as the square (and more at
32), and the kernel's share falls from 19% to under 2%: the waste is in
elaboration [measured]. Sixteen constructors of two fields cost 2.33M
against eight's 1.14M, so constructors are linear, as SW-3710 found.

This reads std's table differently. `Map.Tree`'s 2.0M is one constructor
with five fields (`Bin size left key value right`), not "two constructors".
`Omega.Fact`'s 4.2M is 16 constructors of two or three fields [checked,
`std/Omega/Omega.sw:116`, `std/Map/Raw.sw:20`].

**Field types matter little.** Eight constructors of two fields: `Nat`
1.14M, `Text` 1.06M, `Bool` 1.44M, `List Nat` 1.46M, a derived enumeration
1.48M, a derived two-constructor type 1.63M, the type itself (recursive)
0.77M [measured]. SW-3710's "about three times more when fields have
derived instances" compared `Fact` with `ITerm`, which differ in fields per
constructor too; on its own a derived field type costs about 1.4 times
[measured; the confounding is inferred].

**Instances in scope don't matter.** Forty unrelated enumerations declared
first (80 more instances) leave `T`'s cost at 1,141,501 steps against
1,141,639 [measured]. So the 27% the profile gave to instance unification
is per mention, not a search that grows with the library.

### 2.3 Three causes, each isolated

**(a) Reading a field's equation out of the conjunction is cubic.** The
congruence `C a… = C b…` alone, as a theorem in source, in the deriver's
shape (`gen2.py`):

| Fields | Hypotheses given one by one (`congJ`) | Read from one conjunction by `And.left (And.right …)` (`congConj`) | Same, each tail named once in a `let` (`congConjLet`) |
|---|---|---|---|
| 4 | 1.6K | 10.9K | 5.7K |
| 8 | 3.3K | 103K | 20.1K |
| 16 | 9.1K | 1.15M | 75.1K |

The `J` chain that SW-3710's profile pointed at (`infer_j` 37%) is cheap in
itself: 9K steps for 16 fields. What costs is its third argument: a
projection chain `k` deep whose every level infers implicit arguments the
size of the remaining conjunction, for each of `f` fields [measured; the
mechanism inferred]. `infer_j` is inclusive of that. Naming each tail once
turns the cube into a square, 15 times cheaper at 16 fields.

**(b) The elaborator has a slow path for `(d).holds` in a chain.** No
proofs, only a function body: 32 comparisons joined by `&&` (`gen4.py`):

| Written as | Steps, 8 | Steps, 16 | Steps, 32 | Elab ms, 32 |
|---|---|---|---|---|
| `Nat.equal a b && …` | 1.9K | 5.1K | 11.7K | 1.8 |
| `a == b && …` | 5.0K | 16.5K | 54K | 6.9 |
| `(Nat.decEq a b).holds && …` | 10.5K | 64.6K | 465K | 75 |
| `(DecEq.decide a b).holds && …` (what the deriver writes) | 37.4K | 225K | 1.54M | 258 |
| the same, each test in a `let` first | 22.7K | — | 299K | 41 |

`a == b` *is* `(DecEq.decide a b).holds`, yet written out it costs 28 times
more at 32 terms and grows as the cube (6.8 times per doubling) where `==`
grows as the square. Giving the instance by name saves a third; the rest is
in elaborating a record projection of an application under a nested `&&`
[measured; I did not find the cause, and the "frames" column, 95 against 2,
suggests the nesting]. This is a defect in the elaborator, not in the
derivers, and any hand-written code of this shape pays it too. The test
function `T.%same` itself, which SW-3710 called "a few thousand" steps, is
1.5M at 32 fields because of it.

**(c) Everything is stated two or three times.** `WHOLE` is elaborated in
`%sameSound` and again in `%sameComplete`; the congruence again in `%equal`,
which SW-3710 measured as the dearest single proof (2.32M of `Fact`'s 4.2M).

A fourth, latent: each field's `T.%C%k%at` is a case over all `n`
constructors (`derive_at_in`, `derive.rs:1124`), so a type with `n`
constructors of `f` fields gets `n·f` definitions of `n` branches: quadratic
in constructors. The branches are tiny and it didn't show up to 32
constructors, but it is there [checked; cost inferred small].

### 2.4 Is it inherent?

No. What is inherent: a proof per constructor that mentions each field a
constant number of times, so work linear in the type's total fields. What
the measurements show is `f³` per constructor, from (a) and (b), times
three from (c). Generating source rather than terms is not the cause: the
same source shape written to avoid the deep chains elaborates cheaply
(§3.4). Nor is the rebuild via `J` and `%etaAt`, nor the case-per-constructor
structure, nor pairs of constructors (SW-3370 removed those).

## 3. Option C: cheap proofs

### 3.1 Fix the elaborator's slow path (C1)

Profile cause (b) on the 32-term chain (a ten-line reproducer) and fix it
where it is. It needs no change to what is generated, changes no hashes,
and helps hand-written code. If `(DecEq.decide a b).holds` cost what
`a == b` does, `T.%same` at 32 fields would fall from 1.5M to about 54K, and
every proof that restates the tests with it [inferred]. Opus (the
elaborator's inference), about 1.5 h [estimated from similar profiling
lanes].

### 3.2 Reshape the generated proofs (C2)

In rising order of change:

1. **Name each tail once.** `let q1 := And.right q; let q2 := And.right q1`
   rather than chains. Cubic to quadratic for that part (table (a)).
2. **One congruence lemma per constructor**, `T.%C%cong : a0 = b0 → … →
   C a… = C b…`, proved once by the `J` chain (9K steps at 16 fields) and
   used by `%sameSound` and by the order's `%equal`. Removes (c) for the
   congruence.
3. **State the decision once**, as a definition `T.%C%dec a… b… :
   Decidable (C a… = C b…)`, used by both `%sameSound` and `%sameComplete`.
4. **Decide through a tuple** (§3.4): pack the fields into nested pairs,
   decide the pairs' equality with core's `Pair.decMk`, and carry it back
   with one `Eq.cong`. This replaces the `J` chain, the conjunction and
   `And.Both` altogether.

Opus (it generates what the kernel checks, and the definitional reading
`r == s` computes to `a0 == b0 && …` must survive), about 2 h [estimated].

### 3.3 A budget, so it stays fixed

A test beside `import_cost.rs`: a 16-field record and a 16-constructor,
three-field type, each under a step count. The target I would set: linear
in total fields, at most about 15K steps per field for all four instances
together [my proposal]. Today's 16-field record is at 1.2M per field.

### 3.4 Prototype of the tuple shape [measured]

Written by hand as source for a one-constructor type (`gen3.py`): the
function `R.same` exactly as the deriver writes it, `R.pack` and `R.unpack`
between `R` and `Pair Nat (Pair Nat …)`, one decision, and both proofs:

```text
def R.dec: (r: R) → (s: R) → Decidable (r = s)
  | MkR a0 a1 a2, MkR b0 b1 b2 =>
      Decidable.map
        (Pair.decMk a0 b0 (MkPair a1 a2) (MkPair b1 b2) (DecEq.decide a0 b0)
          (Pair.decMk a1 b1 a2 b2 (DecEq.decide a1 b1) (DecEq.decide a2 b2)))
        (e => Eq.cong R.unpack e) (e => Eq.cong R.pack e)
theorem R.sound …   | MkR a…, MkR b…, h => Decidable.sound (R.dec (MkR a…) (MkR b…)) h
theorem R.complete … | MkR a…, MkR b…, e => Decidable.complete (R.dec (MkR a…) (MkR b…)) e
```

It checks: the decision's `holds` computes to `R.same`'s body, so `h` has
the right type with no rewriting. Steps for all six definitions, against
the deriver's whole output for the same type (of which `==` is about a
third, by SW-3710's split):

| Fields | Prototype, all of `==` | Of which `R.same` itself | Deriver, everything | Deriver's `==` third [estimated] |
|---|---|---|---|---|
| 4 | 34K | 8.8K | 278K | 93K |
| 8 | 109K | 39K | 1.97M | 0.66M |
| 16 | 495K | 229K | 19.3M | 6.4M |
| 32 | 2.96M | 1.55M | 233M | 78M |

So 3 times cheaper at 4 fields, 13 at 16 and 26 at 32, and half of what
remains is `R.same`, which C1 would shrink. The two proofs themselves are
23K steps each at 16 fields. It uses only lemmas the core already has, and
a recursive field is handled as today (a decision made of `T.%same` and
its proofs, passed to `Pair.decMk`), since `Pair.decMk` takes decisions of
particular equations, not an instance. The order's three laws would need
the same idea worked out (`Pair.compareWith`'s laws take comparison
functions, which a recursive field can't supply unapplied); that is the
part of C2 I have not prototyped.

### 3.5 What C saves

- **Users' wide types:** from the cube to a square or better. A 16-field
  record from 1.6 s to perhaps 0.1 s, a 32-field one from 30 s to under 1 s
  [estimated from the prototype's ratios, applied to all four instances;
  the order's half is unproven].
- **Std's import:** less than one would hope, because std's internal types
  are narrow (two or three fields), where the prototype gains 2 to 3 times.
  Nat's 9.5M extra steps to perhaps 4M to 5M, 0.6 s to about 0.3 s
  [estimated, low confidence]. C alone does not return the import to its
  old cost; D does.
- **Trust:** unchanged. Everything is still source the elaborator
  elaborates and the kernel checks; C1 is an elaborator speed fix.
- **Hashes:** every derived declaration's changes once (C2). Not counted.

## 4. Option D: one std cache per machine

**Measured.** `import Std (Nat)` and one definition: 1.92 to 2.01 s with
`--no-cache`; 0.33 to 0.34 s once `.stitchwort/cache/check/` holds std's
entries; 0.27 to 0.29 s for a program with no import. So replaying std's
files costs about 0.06 s, and derived instances are a rounding error in it.
The entries for this program are 2.1 MB.

**Why it isn't already so.** D281 (check-cache.md §6): entries live in the
project's `.stitchwort/cache/check/`, library files' too, and a user-level
cache "is not worth having yet. The fingerprint changes with every build
of the compiler, and every lane builds its own, so a shared cache would
rarely hit. Revisit when there are releases." That reasoning is about
compiler developers. For anyone using one build of the compiler across
several folders (every single-file `check` in a new folder, every new
project, every AoC day opened on its own) the shared cache hits every time
after the first.

**The change.** Library-file entries go to a per-user folder
(`~/.cache/stitchwort/check/`, or what the platform says), still named
`{fingerprint}-{unit}-{key}`; project namespaces stay per project. The
per-project salt in `check/header` needs a per-user equivalent. Entries of
other fingerprints are already pruned after a day. Later, a release (the
Nix package) can ship the folder pre-filled, as the playground ships
`pkg/std.cache.gz` (2.3 MB gzipped for all of std).

**Trust.** The same as today's cache, which is read without re-checking: an
entry is trusted because its key covers the compiler, the file and its
dependencies. A per-user folder is writable by the same user as the
project's. A shipped cache is trusted as the binary is: both come from the
same build.

**What it doesn't help.** Runs that check std from source on purpose: the
tiers' `--no-cache` checks, `import_cost.rs`, a lane after editing std, and
any test that loads std from source in its own session. Those keep paying
the derived instances' cost, which is where C counts for std. Nor does it
help users' own types.

**Build.** Sonnet, about 1 h for the per-user folder; shipping a filled
cache with the Nix package another hour when there are releases
[estimated].

## 5. What other systems do [cited, fetched 17 November 2026]

| System | Derived by default? | Laws proved? | Eager or lazy | Cost evidence |
|---|---|---|---|---|
| Lean 4 | No: `deriving DecidableEq, BEq, Ord` is opt-in | `DecidableEq` carries its proofs. `ReflBEq`, `LawfulBEq` derivable since 4.25 by "a dedicated, syntax-directed tactic", not for mutual or nested types ([release notes](https://lean-lang.org/doc/reference/latest/releases/v4.25.0/)). **No `Ord` laws**: a draft, [#14929](https://github.com/leanprover/lean4/pull/14929), is unmerged | Eager. `noConfusion`, `below`, `brecOn`, `sizeOf`, injectivity are all made at declaration ([`MutualInductive.lean`](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/MutualInductive.lean)) | [#10152](https://github.com/leanprover/lean4/pull/10152): the usual `DecidableEq` "is necessarily quadratic in size"; a linear construction from 10 constructors up. [#8037](https://github.com/leanprover/lean4/pull/8037), linear-size `noConfusionType`: a RISC-V syntax tree from 60 s to 6 s. [#15508](https://github.com/leanprover/lean4/issues/15508): a derived `DecidableEq` regression, 0.21 s to 10.5 s, open |
| Rocq | No: `Scheme Equality for T`, "tries to generate a Boolean equality and a proof of the decidability" ([manual](https://rocq-prover.org/doc/v8.13/refman/user-extensions/proof-schemes.html)) | Yes, limited for mutual and nested types | On request | coq-elpi's `derive`: the newer `eqb`/`eqbOK` run "in linear time/space", the older "quadratic" ([README](https://github.com/LPCIC/coq-elpi/blob/master/apps/derive/README.md)); Grégoire, Léchenet and Tassi's `feqb` (CPP 2023): terms and proofs "grow linearly with the type's size" ([abstract](https://popl23.sigplan.org/details/CPP-2023-papers/17/Practical-and-sound-equality-tests-automatically)) |
| Agda | No built-in deriving | Library tactics build `Dec (x ≡ y)` | On request | stdlib-meta's [`Tactic.Derive.DecEq`](https://agda.github.io/agda-stdlib-meta/Tactic.Derive.DecEq.html) is a clause per pair of constructors; a [`DecEqFast`](https://agda.github.io/agda-stdlib-meta/Tactic.Derive.DecEqFast.html) variant "typechecks faster in the presence of many fields/constructors" |
| Idris 2 | No | `DecEq` through idris2-sop's generic representation ([docs](https://stefan-hoeck.github.io/idris2-sop/docs/md/Deriving.html)); no `Ord` laws found | On request | none found |
| Isabelle/HOL | Yes: a datatype's theorems | Yes | Eager | A 50-constructor datatype about 30 s, 3 s with plugins off; the old package's lazy distinctness simproc was dropped: "a deliberate decision to get rid of this special case" ([users' list, 2021](https://isabelle.systems/zulip-archive/stream/247541-Mirror.3A-Isabelle-Users-Mailing-List/topic/.5Bisabelle.5D.20Datatype.20definition.20can.20be.20slow.html)) |

Three things follow.

- **Stitchwort does more than any of them**: no system above proves the
  order's laws for every type automatically, and only Isabelle derives
  anything without being asked. Derived `<` is two thirds of the cost
  (SW-3710). That is a reason to make it cheap, and it is also the honest
  alternative if it can't be made cheap: derive `==` always and `<` on
  request. I don't recommend that now, since §3 says it can be made cheap.
- **Everyone who hit this cost made the construction linear; nobody made
  it lazy.** Lean's fixes (#8037, #10152) and coq-elpi's are size
  reductions of an eager construction, and Isabelle removed its one lazy
  special case. I found no lazily generated auxiliary definitions in Lean
  [searched, not found; unverified that none exist].
- **Lean is moving towards Stitchwort's shape** (a `Bool` test plus law
  proofs) and away from proof-carrying `Decidable` (#15508's discussion,
  #14929). Rocq's `feqb` is the same shape with linear proofs, which is
  evidence that linear is reachable.

Not verified: Rocq's defaults for the equality-scheme flags, the details of
`feqb`'s technique (I read the abstract only), and whether any system ships
description-based (generic) deriving for user types by default; I found
none.

## 6. The other questions

### 6.1 Do the laws need a proof per type? (G: a generic theorem)

The idea: describe each type by a code (a sum of products of field types),
prove once that the `==` computed from any code is sound and complete and
that its `<` is an order, and give each type its laws through the
correspondence between the type and its code.

What stays per type is that correspondence: a function each way and the
proofs that they undo each other, a case per constructor, plus a proof
that the direct `T.%same` (which must stay, both to run fast and so `r ==
s` computes to `a0 == b0 && …`) equals the generic test on the code. So
the per-type work is still a case per constructor mentioning every field;
it removes the cube only in the sense that any linear shape does. Against
it: recursive, nested and mutual types need codes with fixed points, and
the generic `==` over them must pass the termination checker, which is the
problem nested types already forced members on (derived-equality.md §2);
checking the per-type equations runs an interpreter over codes in the
elaborator; and no system above ships it as its default. Trust would be
unchanged (all of it is checked).

The tuple shape of §3.4 is the part of this idea worth having: products
handled generically by `Pair`'s lemmas, sums by the tag lemmas the core
already has (`DecEq.tagsSame`, `Ordering.tagsEqual`, …). The current
design is already "generic over sums"; C2 makes it generic over products.
A full universe of codes: Opus, 8 h or more, with a real chance of not
landing [estimated]. Not recommended.

### 6.2 A kernel-level fact? (K)

The kernel could decide structural equality of first-order data itself and
supply the law as a rule. I advise against it:

- 80% of the time is elaboration and 19% the kernel (SW-3710), falling to
  under 2% for wide types (§2.2). The kernel isn't where the cost is.
- Derived `==` isn't purely structural: a field's test is that field
  type's instance, which may be hand-written (a quotient's, `Float`'s),
  and proof fields are skipped by Hedberg's argument. A kernel rule would
  cover a subset and the derivers would stay for the rest.
- The order's laws, two thirds of the cost, would need a second rule.
- It moves a deriver's reasoning into the trusted base. Today a bug in a
  deriver gives a proof the kernel rejects; with a rule it could give a
  false theorem.

A smaller kernel fact, built-in constructor injectivity and disjointness,
would remove the `T.%C%k` projections and `%at` helpers, but those are not
where the steps go.

### 6.3 Functions now, proofs later? (F)

The instance can't be split as it stands: `DecEq`'s `decide` returns a
`Decidable`, a record whose `sound` and `complete` fields are the proofs,
so the instance's term mentions them and the kernel needs them defined
[checked, `core/DecEq.sw`, `core/Decidable.sw:21`]. Two ways to defer
anyway:

- **Defer the whole instance** until first use. That is option A; the
  functions are free, so nothing is gained by keeping them eager.
- **Declare each law with its type and check its body later**: at the end
  of the session, on another core, or only for `check` and not `run`. The
  kernel has no definitional proof irrelevance (docs/core.md, line 145), so
  this needs laws marked so that nothing unfolds them; then it is sound as
  long as "checked" is reported only after every deferred body passes. For
  a cold `check` it saves no work, only wall-clock if other cores are used
  (Lean elaborates theorem bodies in parallel on this principle
  [from memory, unverified]). Skipping the bodies for `run` would mean
  running a program whose library wasn't fully checked, which is what D
  gives soundly: checked once, by the same compiler, remembered.

Checking on other cores is a real direction for the checker as a whole, but
an architectural one; nothing here needs it.

### 6.4 Is "derive for everything" right for std's internal types?

The twelve reflection types and `Map.Tree` are never compared, and
`Map.Tree`'s structural `==` isn't map equality. D3609's own risk note
called these "internal". So there are two honest positions:

- *Right, and it must be cheap.* One rule, no exceptions, nothing for a std
  author to remember; the cost is an implementation matter. A user's
  reflective syntax (their own tactic's terms) is the same kind of type and
  can't be exempted by a std-only list, so cheapness is needed anyway.
- *An opt-out is a feature in its own right* (F#'s `[<NoEquality>]`): for a
  type whose structural equality would mislead, not for cost.

I hold the first for cost and think the second should be decided on its own
merits, if a case comes up where a derived `==` is harmful rather than
merely unused; none has. A user can already replace an instance; what
nobody can do is say "none".

For users' own types, A and B do nothing as proposed (both are std-only),
and making A general would mean a program's types are derived when first
compared, which moves the cost rather than removing it. C is the only
option that helps them.

### 6.5 Smaller ideas

- **Share between `==` and `<`.** The congruence lemma (§3.2, item 2) is
  the sharing that pays: `%equal` is the dearest proof and rebuilds it.
- **`==` from `<`.** `r == s` could be "`compare r s` is `Equal`", with
  `%equal` as its soundness, dropping `%sameSound` and `%sameComplete` (a
  third of the cost). But then `r == s` no longer computes to `a0 == b0 &&
  …`, which the readings and `rfl` proofs rely on, and types with `==` but
  no order (quotients' fields) still need the direct path. No.
- **`<` from `==` plus a rank.** That is what the tag comparison already
  does between constructors; within one constructor the fields' orders are
  needed.
- **Caching by shape.** `Omega.Env` and `Ring.Env` are the same shape, and
  a proof depends only on the shape. With the tuple shape the sharing is
  automatic where it matters (the `Pair` lemmas are proved once); a cache
  of whole proofs by shape would add a mechanism for what the check cache
  already does per file.
- **Direct terms instead of source** (SW-3710's C). It would skip
  elaboration, but §2.3 says elaboration is slow because of two fixable
  causes, and writing 6,000 lines of derivers as raw terms gives up the
  elaborator's checking of them as they're built. Not needed.

## 7. Questions for Matt

**Q1. Fix the cost where it arises and keep deriving everything eagerly,
rather than deriving std's instances on first use (SW-3710's
recommendation, A)?** [rec: yes]

- *The problem.* Derived proofs cost the cube of a constructor's fields: a
  16-field record takes 1.6 s to declare and a 32-field one 30 s. Std's
  slower import is the first place it showed, not the worst.
- *The change.* SW-3719 becomes two lanes: fix the elaborator's slow path
  on chains of `(d).holds` (§3.1), and reshape the generated proofs
  (§3.2), with a step-budget test for a wide record and a many-constructor
  type. No derive-on-first-use, and no opt-out syntax.
- *What it should do.* A 16-field record from 1.6 s to about 0.1 s
  [estimated; the `==` half measured on a prototype at 13 times cheaper];
  std's extra import cost roughly halved [estimated, low confidence]; every
  type still has its instances the moment it is declared.

**Q2. Keep std's check-cache entries in one folder per user, shared by all
projects, and ship it filled once there are releases? (This reopens D281.)**
[rec: yes]

- *The problem.* Every new folder pays the whole of std again: 1.95 s for
  a program importing `Nat`, of which derived instances are a third.
- *The change.* Library-file entries move from each project's
  `.stitchwort/cache/check/` to a per-user folder; nothing else about the
  cache changes.
- *What it should do.* After the first run on a machine, a cold start in
  any folder takes about 0.35 s instead of 1.95 s [measured with a warm
  project cache]. Checks that read std from source on purpose (the tiers,
  std's own lanes) are unaffected.

## Appendix: the probes

All run as `STITCHWORT_TIMINGS=decls nice -n 19 stitchwort check --no-cache
FILE`, reading the `Main.…` rows. A type's row includes everything derived
for it.

- `gen.py NAME ctors fields fieldtype …`: `type NAME = | NAMEK0 (f0: T) … |
  …`, several types in order. §2.2's tables.
- `gen2.py f`: `type R = | MkR (f0: Nat) …` and the congruence `MkR a… =
  MkR b…` four ways: `congJ` (a `J` per field, hypotheses `h0 … h(f-1)`),
  `congConj` (the same with each `hk` replaced by `And.left (And.right^k
  q0)` from one right-nested conjunction), `congConjLet` (tails bound by
  annotated `let`s first), `congTrans` (`Eq.trans` of `Eq.cong`s: 148K at
  16 fields, dearer than the `J` chain).
- `gen3.py f`: §3.4's six definitions.
- `gen4.py f`: one `def … : Bool` per row of §2.3 (b), over `a0 … b(f-1):
  Nat`, the chain nested to the right.
- Cache: `printf 'import Std (Nat)\ndef n : Nat := Nat.gcd (Nat.pow 3 4)
  (Nat.max 6 9)\n' > n.sw`, then `time stitchwort check --no-cache n.sw`
  three times and `time stitchwort check n.sw` four times in an empty
  folder (the first fills the cache: 2.17 s).

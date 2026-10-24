# Effect polymorphism: one function for pure and effectful callbacks

Status: design note and literature review, revised after external review,
24 Oct 2026. The row type is now spelled `Effects` in source (D1143 (a)); the
older sections below still say `Row`, its earlier name. Decided (Matt, 24 Oct 2026): D1116 to D1126 as recommended in
§7, so design C with stage 0 first. Stage 0 is built ("As built (stage 0)", before the appendices), and the first part of stage 1 ("As built (stage 1, first part)"), which leaves D1133 and D1134 as options for the owner. The two experiments before this note are in
[effectful-map.md](effectful-map.md).

Claims about the codebase cite `file:line` and are marked **[checked]** (read
in the source on `main` at `754128ca`, or for the revision at `2934c86e`, or
run with `target/release/stitchwort` built from `main` on 24 Oct 2026 and
Node 22.23.3) or **[inferred]**. Claims about other languages and papers
cite a URL. **[unverified]** marks claims written from memory without a
source I could open. The probe files are in Appendix A, so a reader can
rerun them.

## Changes after review

An external reviewer read the first version. They approved stage 0, C with
E, F as a separate stage, incremental adoption and deferring `Partial`.
They asked for B to be rejected more firmly, and blocked implementation on
one point: the unification rule. Each point and what changed:

| Review point | Change | Where |
|---|---|---|
| §3: "head is not `Comp`, so `Empty`" is too eager (blocking) | Replaced by an apartness rule: solve `?e := Empty` only when the other type can never become a `Comp`; postpone when it is blocked; a separate rule for a rigid `Comp`. Postponed constraints are retried in the elaborator's existing end-of-declaration rounds. Defaulting an unsolved row to `Empty` is now a separate step after solving, with eligibility conditions. Worked examples. | §5.C.1, D1123, D1124 |
| §2, §9: `Empty` versus `Ops NoOp NoRes`; rows as user data | `Row` becomes a library-internal index: programs can't construct, inspect or compare rows. Canonical-form invariant stated, with what checks it. Rows are an index semantically and a one-bit runtime argument operationally; E removes it. New probes show that today a program *can* build, pass, return and match a row value (probe 9). | §5.C.2, D1122 |
| §1: universe levels | Abilities' operations are always in `Type 0` today (probe 10). `Row: Type 1` kept, with the limitation written down; `Row u` is the extension path once universe polymorphism exists. | §5.C.3, D1125 |
| §5: reject B | B is marked rejected unless C proves infeasible for reasons much stronger than implementation cost. The analysis is kept. | §5.B, D1116 |
| §4: stage 0 acceptance | An observational test added. New probe 8: today even a bare *variable* of type `Comp NoOp NoRes a` is run in place when passed as an argument; the cause is found (`may_perform`). Every path that runs a computation in place is listed, each with a test. | §5 stage 0, §6 |
| §6: E as an invariant, not as "`map` gives the same JS" | E is specified as generic partial evaluation on a fixed set of representation-driving parameters (initially only `Row`), with a code-size policy. `map` is the test case. The cache key is unchanged. | §5.E, §6 |
| §7: don't freeze CPS | Stage 4's requirement is stated first (amortised O(1) `bind`, no rebuilt chains on resumption, stack safety in JS); CPS with a trampoline, a type-aligned continuation queue and evidence or capability passing are candidates for stage 4's own design note. | §5.F, D1119 |
| §8: proof tooling | A small algebraic library of named lemmas, not an interaction-trees framework. | §5 "Proof tooling", D1126 |
| §1 wording: prior art | C is described as an effect-indexed computation family with a representation-changing pure index; F★ indexed effects and graded monads are cited for the shape; no exact precedent for `CompIn Empty a ≡ a` was found. The Koka framing is corrected. | §3.1, §3.2 |

Where the codebase differed from the review or from the first version:

- The reviewer says a constraint against an unknown type `?T` should wait.
  In Stitchwort the ordinary unifier solves `?T := CompIn ?e B` instead,
  which commits nothing about `?e` (`unify.rs:194-197`) **[checked]**. No
  row constraint arises. §5.C.1.
- The reviewer suggests documenting defaulting "like numeric defaulting".
  Stitchwort's number defaulting is eager: a literal checked against an
  unknown type makes it `Nat` at once (`numbers.rs:291-312`) **[checked]**.
  There's no defaulting phase after solving. The phase that does exist is
  the end-of-declaration rounds for auto arguments and instances
  (`lib.rs:831-834`, `auto.rs:62-99`) **[checked]**; row defaulting goes
  there.
- The first version's Appendix B said there's no syntax for giving an
  implicit argument by hand. Named implicit arguments `[op := …]` exist now
  (probe 9) **[checked]**.
- The first version said probe 4's argument was run in place because it is
  a call. Even a bare variable is (probe 8) **[checked]**.

## 0. Summary

The owner wants one `List.map` that takes either a pure or an effectful
callback, as in Unison, on two conditions: the proofs about `map`
should keep working, and pure uses should run as fast as today. The two
earlier attempts failed on both counts.

What this note finds:

1. **The proofs get stuck because `bind` asks the wrong question.**
   `Effect.bind` decides what to do by looking at the computation (`Done` or
   `Call`). Inside `map`'s body the computation is `map f xs` for a variable
   `xs`, so nothing reduces. But the thing that is known at a pure use is the
   *row*: it is empty. If `bind` looked at the row first, it would reduce at
   the empty row whatever the computation is. A probe confirms it: with a row
   type `Empty | Ops op res` and a computation type defined by cases on it,
   the folded `map` at the empty row satisfies `map Empty f xs = List.map f
   xs` and `List.lengthMap` by `Eq.cong` alone, exactly as today's proofs
   do (probe 5, §4). No kernel change is needed.
2. **Speed needs a backend pass anyway.** Every design leaves a row argument
   and some dispatch in the generated code. The fast loop comes back only if
   the backend makes a copy of a row-polymorphic function for the empty row
   and simplifies it. With the row-indexed type, that copy is ordinary
   constant folding: `bindIn Empty c k` is `k c` by its own definition. The
   simplified copy of the folded `map` is the same code as today's
   tail-recursion-modulo-cons loop.
3. **The effectful case has a second problem, not recorded before.** An
   effectful `mapIn` whose callback really suspends takes time quadratic in
   the list's length, on both backends: 32,000 elements take 62 s natively,
   and JS runs out of stack at about 4,000 (probe 7, §4). The cause is the
   left-nested `bind`s that free-monad encodings are known for (Voigtländer
   2008). The known fixes reassociate the binds at runtime: a
   continuation-passing representation, a queue of continuations, or
   handler evidence passed down as Koka does.
4. **One source-language fix is needed by every design.** Today a
   computation passed as an argument at the empty row is always run in place
   and re-wrapped as `Done (runPure c)`, even when the parameter's type is a
   `Comp`, and even when the argument is just a variable (probes 4 and 8).
   So no lemma about a stuck computation can ever be used. Passing the
   computation unchanged when a computation is expected fixes this, and
   makes `runPure (mapIn f xs) = map f xs` provable.

**Recommendation** (D1116 to D1126): adopt the row-indexed computation type
(design C), preceded by the argument-passing fix (stage 0) and followed by
empty-row specialisation in both backends (design E). Under C, the row is a
library-internal index that programs can't construct or inspect (D1122),
and the elaborator infers the empty row only when the other type can never
be a computation (D1123). Fold `mapIn` into `map` only after both, and
extend the convention to other functions one at a time as programs need
them. Fix the quadratic effectful case as its own stage, against a stated
requirement, choosing the runtime representation in that stage's own design
note (design F).

## 1. How abilities work in Stitchwort today

This section is for a reader who doesn't know Stitchwort.

Stitchwort is a dependently typed language with a small kernel. Abilities
(algebraic effects) are not a kernel feature. The elaborator translates them
into ordinary data defined in the prelude, and the kernel re-checks the
result (`crates/elab/src/effects.rs:1-20`, `docs/core.md` "Abilities")
**[checked]**.

A computation is a tree (`crates/elab/src/std/core/Effect.sw:12`)
**[checked]**:

```
type Effect.Comp (op: Type) (res: op -> Type) (a: Type): Type =
  | Done (value: a)
  | Call (o: op) (rest: res o -> Comp op res a)
```

`op` is the type of operation calls and `res o` is what call `o` returns.
`bind` sequences two computations by cases on the first
(`Effect.sw:25`), `foldComp` is the fold that handlers are made of
(`Effect.sw:19`), and `runPure` takes the value out of a computation over
the signature with no operations (`Effect.sw:145`):

```
def Effect.bind: [op: Type] -> [res: op -> Type] -> [a b: Type] ->
    Comp op res a -> (a -> Comp op res b) -> Comp op res b
  | Done x, next => next x
  | Call o rest, next => Call o (y => bind (rest y) next)

def Effect.runPure: [a: Type] -> Comp NoOp NoRes a -> a
  | Done x => x
  | Call () rest
```

(`Call () rest` is an absurd pattern: `NoOp` has no values.)

A row such as `{Abort, IO | e}` becomes a chain of `Plus` types of the
abilities' operation types, ending in `NoOp` (a closed row) or in `sigOp e`
for a row variable `e: Sig`, where `Sig` packs an operation type and its
result function (`Effect.sw:104`). A function type `a -> {E} b` is
`a -> Comp (ops of E) (results of E) b` **[checked]** (`effects.rs:5-12`).

Effectful code is written in direct style. The elaborator inserts `Done`,
`bind`, `Call` and `translate` (moving a computation from one row to a
larger one). Two rules matter here:

- **D1055, run in place at the empty row.** In pure code (the empty row), a
  call that would be sequenced with `bind` is run where it stands instead,
  as `runPure c` bound by a transparent `let`
  (`docs/proposals/abilities.md:259-265`, `effects.rs:1489`) **[checked]**.
- **SW-393, pure callbacks.** A pure function passed where an effectful one
  is expected is wrapped as `x => Done (f x)` (`effects.rs:2543`,
  called from `check.rs:2204`) **[checked]**.

Today the library has a pure `List.map` and an effect-polymorphic
`List.mapIn` with the same equations (`crates/elab/src/std/List/Toolkit.sw:13-24`)
**[checked]**:

```
def List.map (f: a -> b): List a -> List b
  | Nil => Nil
  | Cons x xs => Cons (f x) (List.map f xs)

def List.mapIn (f: a -> {e} b): List a -> {e} List b
  | Nil => Nil
  | Cons x xs => Cons (f x) (List.mapIn f xs)
```

`mapIn`'s `Cons` case elaborates to
`bind (f x) (y => bind (mapIn f xs) (ys => Done (Cons y ys)))`.

The backends know nothing about effects. The JS backend compiles `Comp` as
ordinary tagged objects and `bind` and `runPure` as ordinary functions
(probe 6) **[checked]**. Its only special shape is self tail calls, including
tail recursion modulo constructor, which turns `map` into a loop that fills
in each cell's tail (`crates/js/src/lib.rs:1910-1931`, `lib.rs:2165`)
**[checked]**. The native runtime `crates/rt` runs its own frame stack
(`crates/rt/src/lib.rs:1-12`) and recognises `y => Done y` continuations to
run tail requests in constant space (`crates/rt/src/erasure.rs:115-127`)
**[checked]**.

## 2. Scope of the problem

### 2.1 Std functions that take callbacks

A scan of `crates/elab/src/std/` for definitions with a function-typed
parameter finds about 110, not counting `Show` printers, `Prop`-valued
predicates and helper steps **[checked]**. The ones a program could
plausibly want with an effectful callback (a parser that fails, a counter,
logging, a lookup that aborts):

| Family | Functions |
|---|---|
| List (`List/Toolkit.sw`, `List/Sort.sw`, `List/Unfold.sw`) | `map`, `filter`, `filterMap`, `flatMap`, `concatMap`, `foldLeft`, `foldRight`, `scanLeft`, `mapAccumLeft`, `zipWith`, `zipWith3`, `any`, `all`, `find`, `findMap`, `findIndex`, `count`, `partition`, `takeWhile`, `dropWhile`, `span`, `sumBy`, `maxBy`, `minBy`, `sortBy`, `sortWith`, `sortOn`, `splitBy` |
| Option, Result | `Option.map`, `flatMap`, `fold`, `filter`, `exists`, `forall`; `Result.map`, `mapError`, `flatMap`, `traverse` |
| Map, Set (`Map/Map.sw`, `Set/Set.sw`) | `Map.map`, `mapWithKey`, `foldLeft`, `foldRight`, `filter`, `filterMap`, `partition`, `insertWith`, `alter`, `adjust`, `unionWith`, `fromListWith`, `groupBy`, `any`, `all`, `count`, `find`; `Set.foldLeft`, `foldRight`, `filter`, `map`, `any`, `all` |
| Vec | `Vec.map`, `zipWith`, `foldLeft`, `tabulate`, `traverseOption`, `any` |
| Other | `Text.fold`, `Nat.iterateUntilStable` |

That is about 70 functions. There is no `forEach`, which in Unison is the
most common effectful higher-order function **[checked]** (no match in std).

### 2.2 How many theorems mention them

Counting theorem *statements* (from `theorem` to its `:=` or first clause)
in std that name the function in full **[checked]**, with the script in
Appendix A:

| Function | Statements | Function | Statements |
|---|---|---|---|
| `List.map` | 78 | `List.sumBy` | 51 |
| `Option.map` | 18 | `List.filter` | 17 |
| `List.foldLeft` | 15 | `List.any` | 15 |
| `List.find` | 13 | `List.all` | 10 |
| `List.filterMap` | 10 | `List.count` | 8 |
| `Map.Spec.foldLeft` | 7 | `List.flatMap`, `List.merge` | 6 each |
| `Map.insertWith` | 6 | `List.sortWith`, `List.sortBy` | 5 each |

There are 1,248 theorems in std in all. `effectful-map.md` says "about 58"
mention `map`; by this count it is 78 statements, plus uses in proof bodies
**[checked]**. Whatever the design, these statements are the migration cost
if pure behaviour isn't definitional.

### 2.3 What Unison does

Unison's base library makes higher-order functions ability-polymorphic by
default. `List.map : (a ->{e} b) -> [a] ->{e} [b]`
([docs: higher-order functions](https://www.unison-lang.org/docs/fundamentals/values-and-functions/_higher-order-functions),
[using abilities](https://www.unison-lang.org/docs/fundamentals/abilities/using-abilities-pt1/)),
`List.foldLeft : (b ->{e} a ->{e} b) -> b -> [a] ->{e} b`
([exercise page](https://unison-lang.org/docs/exercises/values-functions)),
and `Optional.filter : (a ->{g} Boolean) -> Optional a ->{g} Optional a`
(same "using abilities" page). That the whole base library follows the
convention is **[unverified]**: Unison Share pages render client-side and
couldn't be read. Unison's polymorphism comes from an ordinary type
variable, and a type with an empty ability set means "no abilities", unlike
Frank, where an empty set means "polymorphic"
([pre-conference syntax guide](https://unison-lang.org/blog/pre-conference-syntax-guide)).

What differs from Stitchwort: Unison has no proofs, so it never needs
`map f xs` to *reduce* to anything in a type. Its runtime implements
abilities with delimited continuations rather than trees, and it was moving
to a JIT through a Scheme backend ([JIT announcement](https://www.unison-lang.org/blog/jit-announce/);
the Chez Scheme detail is **[unverified]**). So Unison shows the convention
is pleasant to use, but not how to keep proofs and speed with a tree
encoding.

## 3. Literature and state of the art

Each entry ends with what it would mean for Stitchwort.

### 3.1 Compiling effect polymorphism efficiently

**Koka: row-polymorphic effect types** (Leijen, "Koka: Programming with
row-polymorphic effect types", 2014,
[PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-20.pdf);
the venue, MSFP 2014, is **[unverified]**). Read in the PDF: `map` has the
type `map : ∀αβµ. (list⟨α⟩, α → µ β) → µ list⟨β⟩`, "where the effect of the
map function itself is completely determined by the effect of its
argument". Koka's effect row tracks effects in types; a computation keeps an
ordinary value representation in the language. So Koka is precedent for
higher-order functions quantifying over their callback's effect, which is
what the owner wants. It is *not* precedent for design C's definitional
equation `CompIn Empty a ≡ a`: Koka has no proofs and no tree encoding that
would need it **[inferred]**.

**Koka: selective CPS** (Leijen, "Type directed compilation of row-typed
algebraic effects", POPL 2017,
[MSR page](https://www.microsoft.com/en-us/research/?p=337556),
[tech report PDF](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/08/algeff-tr-2016-1.pdf)).
Koka used effect types to decide which functions need continuation-passing
style (CPS: every function takes "the rest of the program" as an extra
argument). Total functions stay direct. Effect-polymorphic functions were
compiled twice, once direct and once in CPS, and the direct copy is used
when the row is known to be total **[unverified]** for the "compiled twice"
detail. *For Stitchwort:* the type of a call site tells the backend the
row; generating a pure copy per row-polymorphic definition is an
established technique (design E).

**Koka: evidence passing** (Xie, Brachthäuser, Hillerström, Schuster,
Leijen, "Effect handlers, evidently", ICFP 2020,
[MSR page](https://www.microsoft.com/en-us/research/publication/effect-handlers-evidently));
(Xie and Leijen, "Generalized evidence passing for effect handlers", ICFP
2021, [PDF](https://www.microsoft.com/en-us/research/uploads/prod/2021/08/genev-icfp21.pdf)).
Handlers are passed down as an "evidence vector", so performing an
operation is a lookup and a call. Two points from the 2021 paper matter
here, read in the PDF:

- Its final step is a *monadic translation* into a datatype with two
  cases, `Pure` and `Yield`: the same shape as Stitchwort's `Done` and
  `Call`. Naively, "every bind operation takes a lambda … many closure
  allocations even for non-yielding code" and "direct tail-recursive calls
  are no longer directly tail-recursive" (§2.10). The fix is
  *bind-inlining* (expand `bind c k` into a `case c of Pure x -> …k…`) and
  *join-point sharing* (name each continuation once so the expansion stays
  linear). This gives "a fast path along each Pure branch: if no operation
  performs a full yield, no allocation happens along this path and
  tail-recursive calls are preserved". Koka also "leaves out monadic binds
  for functions that are total".
- *Tail-resumptive* operations, whose handler clause is `op x k => k e`
  with `k` not in `e`, are run in place, with no capture of the
  continuation (§2.6). "Almost all common operations in practice" are of
  this form, including state.
- In the C backend, the monad isn't a heap object: "we always return
  results normally assuming Pure, and set a (thread-local) flag to indicate
  yielding" (§2.11).

*For Stitchwort:* the kernel's `Comp` tree is the semantics; the backend
may represent it as "a plain return value, or a yield", inline `bind`, and
keep the TRMC loop on the fast path. That is design F. Run-in-place for
tail-resumptive clauses would remove most of the effectful overhead.

**Tail recursion modulo context** (Leijen and Lorenzen, POPL 2023,
[PDF](https://www.microsoft.com/en-us/research/uploads/prod/2023/07/trmc-popl23.pdf);
JFP extended version 2025,
[PDF](https://microsoft.com/en-us/research/uploads/prod/2024/05/trmc-jfp-664eb3438fc91.pdf)).
Generalises tail recursion modulo cons to any "context" with application
and composition laws; instances include evaluation contexts (CPS) and
associative operations. *For Stitchwort:* the JS backend already has the
constructor-context case (`lib.rs:1924`). After empty-row specialisation the
folded `map` is that case. The effectful case could use the CPS-context
instance, which is how a monadic `map` avoids deep recursion.

**Effekt: capability passing** (Schuster, Brachthäuser, Ostermann,
"Compiling effect handlers in capability-passing style", ICFP 2020,
[page](https://pl.cs.uni-tuebingen.de/publications/schuster20capability/));
("Zero-cost effect handlers by staging", tech report 2019,
[page](https://pl.cs.uni-tuebingen.de/publications/schuster19zero/)).
Handlers are passed as explicit capability arguments; the target is
iterated CPS. For a restricted, second-class subset, staging annotations
remove all handler abstraction at compile time, so code that uses no
effects carries no cost. Later work on direct style
(Müller et al., "Back to direct style: typed and tight", OOPSLA 2023,
[page](https://pl.cs.uni-tuebingen.de/publications/mueller23continuation/))
translates CPS code back to direct style where control flow is trivial.
That Effekt's newer backends monomorphise effect polymorphism is
**[unverified]**. Effekt's present surface design is "contextual effect
polymorphism" ([effekt-lang.org](https://effekt-lang.org/)): `map` takes a
block typed `A => B / {}`, the block's effects don't appear in `map`'s type,
and they are handled at the call site. *For Stitchwort:* "zero cost when
unused" is achieved by compile-time specialisation, not by a cleverer
runtime. The same holds for design E. Effekt is comparison material for
the runtime (design F), not a representation to copy: it has no explicit
computation trees.

**Eff: optimising compilation** (Karachalias, Koprivec, Pretnar,
Schrijvers, "Efficient compilation of algebraic effect handlers", OOPSLA
2021, [SPLASH page](https://2021.splashcon.org/details/splash-2021-oopsla/6/Efficient-Compilation-of-Algebraic-Effect-Handlers)).
Eff compiles to OCaml through an explicitly typed core and a final monadic
calculus. Type-and-effect-directed source-to-source rewrites (inlining,
specialising handlers) drastically narrow, sometimes close, the gap to
hand-written code. *For Stitchwort:* the closest analogue of design E: a
monadic core plus type-directed rewrites that are valid because the types
say no operation can happen.

**Links: CPS for handlers** (Hillerström, Lindley, Atkey,
Sivaramakrishnan, "Continuation passing style for effect handlers", FSCD
2017, [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSCD.2017.18)).
CPS translations of handlers, implemented as the JavaScript backend of
Links, with uncurrying for proper tail recursion. *For Stitchwort:* a
worked example of compiling handlers to JS without runtime support; JS has
no tail calls, so it needs trampolining to be stack-safe (SW-396).

**Frank** (Lindley, McBride, McLaughlin, "Do be do be do", POPL 2017;
journal version Convent et al., JFP 2020, DOI
[10.1017/S0956796820000039](https://doi.org/10.1017/S0956796820000039)).
Effect polymorphism is implicit: a function's ability is the "ambient"
one, so `map` needs no row variable in its source type. Unison's design
descends from it. *For Stitchwort:* a surface convenience only; it says
nothing about proofs or compilation.

**Helium** (Biernacki, Piróg, Polesiuk, Sieczkowski, "Abstracting algebraic
effects", POPL 2019) **[unverified]**, no URL opened. Lexically scoped
effect instances and abstraction over effects. Not directly relevant.

**OCaml 5** (Sivaramakrishnan et al., "Retrofitting effect handlers onto
OCaml", PLDI 2021, [arXiv](https://arxiv.org/pdf/2104.00250)). Effects are
untyped; handlers use runtime fibres (separate small stacks), and code that
doesn't use effects pays a mean 1% overhead. *For Stitchwort:* the "pure
code pays nothing" result comes from not encoding effects in values at all.
Stitchwort can't drop the tree in the kernel, but a backend may, as long as
outputs agree (the backends are untrusted, `crates/rt/src/lib.rs:1-5`).

**Free-monad performance.** Voigtländer, "Asymptotic improvement of
computations over free monads", MPC 2008
([Springer](https://www.springerprofessional.de/asymptotic-improvement-of-computations-over-free-monads/2760548);
the Haskell `Codensity` type implements it,
[kan-extensions docs](https://hackage-content-origin.haskell.org/package/kan-extensions-5.2/docs/Control-Monad-Codensity.html)):
left-nested binds over a free monad cost quadratic time; representing the
computation in CPS ("codensity") right-associates them and makes it linear.
Kiselyov and Ishii, "Freer monads, more extensible effects", Haskell 2015
(DOI [10.1145/2887747.2804319](https://doi.org/10.1145/2887747.2804319)):
the continuation in a `Call` node is kept as an efficient queue
("type-aligned sequence", from van der Ploeg and Kiselyov, "Reflection
without remorse", Haskell 2014 **[unverified]**). *For Stitchwort:* exactly
the quadratic behaviour measured in probe 7. Either fix works in a
backend without changing the kernel's `Comp`.

**Specialisation, worker/wrapper, defunctionalisation.** GHC's
`SPECIALISE` pragmas and user rewrite `RULES` (Peyton Jones, Tolmach,
Hoare, "Playing by the rules", 2001 **[unverified]**) are the unproved
ancestor of Lean's `csimp`. MLton and Rust monomorphise every polymorphic
function at its uses **[unverified]**. *For Stitchwort:* specialising on a
*row value* is the same move as specialising on a type, and the row is
known at nearly every call site.

### 3.2 Proofs about effectful code in dependent type theory

**Interaction trees** (Xia, Zakowski, He, Hur, Malecha, Pierce, Zdancewic,
POPL 2020, [arXiv](https://arxiv.org/pdf/1906.00046)). A coinductive free
monad in Coq: `Ret`, `Vis` (an event and its continuation) and `Tau` (a
silent step, for recursion). The monad laws (`bind (ret x) k = k x`,
associativity) hold up to strong bisimulation, a proved relation, not
Coq's definitional equality, and users rewrite with them (setoid
rewriting) **[unverified]** for the lemma names. *For Stitchwort:*
Stitchwort's `Comp` is the inductive version (no `Tau`; `Partial` uses a
separate `Delay`). Being inductive, its laws hold as ordinary equalities
provable by induction, which is simpler than ITrees. But the ITrees
experience says that proofs about effectful code *are* proofs by monad
laws; the library needs those lemmas to be statable (stage 0).

**Free and freer monads in Agda and Coq.** Swierstra and Baanen, "A
predicate transformer semantics for effects", ICFP 2019
([PDF](https://webspace.science.uu.nl/~swier004/publications/2019-icfp-anne.pdf)):
free monads in Agda, with weakest-precondition reasoning for exceptions,
state, nondeterminism and general recursion. McBride, "Turing-completeness
totally free", MPC 2015 **[unverified]**: general recursion as a free monad
in a total language, the idea behind Stitchwort's `Rec`. *For Stitchwort:*
these libraries reason about effectful programs by induction on the tree
and by monad laws. None of them gets pure behaviour definitionally: a pure
use is always a separate lemma.

**Lean 4: `mapM`, `Id`, and proven replacements.** Lean keeps pure
`List.map` and monadic `List.mapM` separate, and links them with lemmas
([`Init.Data.List.Monadic`](https://lean-lang.org/doc/api/Init/Data/List/Monadic.html)):
`List.mapM_pure : mapM (fun x => pure (f x)) l = pure (map f l)` under
`LawfulMonad m`, and `List.idRun_mapM : (mapM f l).run = map (fun x => (f
x).run) l` for `f : α → Id β`. `Id` is defined as `Id α := α`, so pure code
in `Id` is definitionally plain **[unverified]** for the exact definition.
For speed, Lean has `@[csimp]`: a theorem `@f = @g` tells the compiler to
use `g` wherever `f` appears. The library proves
`@[csimp] theorem map_eq_mapTR : @map = @mapTR` so that compiled code uses a
tail-recursive `map`
([`Init/Data/List/Basic.lean`](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/List/Basic.lean)).
`@[implemented_by g]` does the same without a proof, trusting the user
**[unverified]**, no doc page opened. *For Stitchwort:* two lessons. First,
Lean, the most used prover with a compiler, does *not* unify `map` and
`mapM`; it accepts two names and a lemma. Second, `csimp` is a clean way to
separate "definition for proofs" from "code that runs" at the cost of one
theorem, and it doesn't enlarge the trusted kernel (design D).

**Agda rewrite rules** ([docs](https://agda.readthedocs.io/en/latest/language/rewriting.html)).
`{-# REWRITE eq #-}` turns a proved equation into a definitional reduction.
The left side must be a neutral function application; confluence is the
user's problem unless `--local-confluence-check` is on. Cockx, Tabareau,
Winterhalter, "The taming of the rew", POPL 2021 (DOI
[10.1145/3434341](https://doi.org/10.1145/3434341)) gives a modular
confluence check that makes such rules safe for type soundness. *For
Stitchwort:* the standard way to make `runPure (bind c k) =
runPure (k (runPure c))` definitional (design B). It shows what has to be
argued: confluence, termination and subject reduction.

**F\*** (Ahman et al., "Dijkstra monads for free", POPL 2017,
[arXiv](https://arxiv.org/pdf/1608.06499); Maillard et al., "Dijkstra
monads for all", ICFP 2019, [arXiv](https://arxiv.org/pdf/1903.01237)).
Effects are indexed by predicate transformers (weakest preconditions), and
the effect lattice includes a total, pure effect that every other effect
lifts from. *For Stitchwort:* F\* treats pure code as a sub-effect lifted
into larger effects, the same choice as SW-393's `Done` wrapping. It
doesn't offer a mechanism for one definition being definitionally pure at
the bottom of a polymorphic effect **[inferred]**.

**F\* indexed effects and graded monads** (Rastogi, Martínez, Fromherz,
Ramananandro, Swamy, "Programming and proving with indexed effects",
[PDF](https://fstar-lang.org/papers/indexedeffects/indexedeffects.pdf)).
Read in the PDF: F\*'s user-defined effects cover "all forms of indexed
monads", elaborated "into a core language of pure, total functions where
the monadic structure is made explicit". The paper recalls Katsumata's
graded monads (2014): a monad indexed by a monoid `{I, ⊕, ε}`, with
`return : a → G a ε` and `bind : G a i → (a → G b j) → G b (i ⊕ j)`. The
unit grade `ε` is the pure one. Its first example, `gst a t` with
`tag = R | RW`, has the *same* representation (a state-passing function)
at both indices; only a refinement differs. *For Stitchwort:* design C has
this shape: `CompIn` is an effect-indexed computation family, `Row` is the
index, `doneIn` is `return` at any index, and `Empty` plays the unit grade.
What is unusual in C is that the index changes the representation: at
`Empty` the carrier is the plain type `a`. That is what makes the pure
equations definitional.

**Idris** (Brady, "Programming and reasoning with algebraic effects and
dependent types", ICFP 2013, listed on
[idris-lang.org papers](https://idris-lang.org/pages/papers.html)).
An effects DSL embedded as an indexed monad, with resources tracked in
types. *For Stitchwort:* the same embedding idea; pure code and effectful
code remain separate functions.

**Dependent types and effects in theory.** Ahman, Ghani, Plotkin,
"Dependent types and fibred computational effects", FoSSaCS 2016
([record](https://era.ed.ac.uk/handle/1842/28788?show=full)): a calculus
separating values and computations, with a computational Σ-type for
dependency through sequencing. Pédrot and Tabareau, "The fire triangle",
POPL 2020 ([page](https://popl20.sigplan.org/details/POPL-2020-Research-Papers/7/The-Fire-Triangle-How-to-Mix-Substitution-Dependent-Elimination-and-Effects)):
a no-go theorem: with effects you can't have full substitution, full
dependent elimination and effects together. *For Stitchwort:* the encoding
as data sidesteps the fire triangle (effects are values; only handlers
interpret them). The price is that effectful terms in types are trees, not
values, which is exactly the `runPure (bind …)` problem.

**Monadic reflection** (Filinski, 1994 **[unverified]**). Turning a monadic
value into direct-style code and back. *For Stitchwort:* D1055's run in
place is a form of reflection for the empty row; design C makes reflection
at the empty row the identity.

**Definitional monad laws.** I found no system that makes `bind`'s laws
definitional for *neutral* computations in general, other than by rewrite
rules (Agda, and Coq's experimental rewrite rules referred to in the
"taming of the rew" follow-ups). Lean's `Id` makes the identity monad
definitionally trivial because `Id` is the identity *function on types*;
that is the idea design C generalises: dispatch on the effect, not on the
computation. I found no exact precedent for a computation family whose
pure index is definitionally the plain type, `CompIn Empty a ≡ a`, inside a
polymorphic effect. So design C is best described as **an effect-indexed
computation family with a deliberately representation-changing pure
index**: indexed and graded monads give the shape, Lean's `Id` gives the
trick at one fixed index, and C combines them.

### 3.3 What the survey says, in short

- No prover unifies pure and monadic `map` definitionally today. Lean, the
  closest, uses two names, a bridging lemma and a compiler attribute.
- Compilers that make effect polymorphism free when no effect is performed
  all do it statically: Koka's selective translation and fast paths, Effekt's
  staging, Eff's type-directed rewrites. The runtime representation of
  computations differs from the semantic one in all of them.
- Free-monad encodings need a CPS or queue representation at runtime to
  avoid quadratic binds.
- Indexed and graded monads are prior art for the shape of design C. No
  system found makes the pure index definitionally the plain type.

## 4. Probes

The probe sources are in Appendix A. All ran against the release CLI on
`main` at `754128ca`.

**Probe 1: the bridging lemma written directly.** Stating
`runPure (bind c k) = runPure (k (runPure c))` for a parameter
`c: Effect.Comp Effect.NoOp Effect.NoRes a` fails at `c`: "expected
`Comp ?0 ?1 ?2`, but this has type `a`" **[checked]**. This reproduces
`effectful-map.md`. Also, `[Effect.NoOp]` in argument position parses as a
one-element list, so there's no way to give `bind`'s implicit arguments by
hand **[checked]**.

**Probe 2: a monomorphic bind by cases.** With
`bindNo: Comp NoOp NoRes a -> (a -> Comp NoOp NoRes b) -> Comp NoOp NoRes b`
written by cases, and `runPureNo` likewise, the bridging lemma
`runPureNo (bindNo c k) = runPureNo (k (runPureNo c))` *is* stated and
proved by cases (`| Done x, k => rfl` and an absurd `Call ()` case)
**[checked]**. So `effectful-map.md`'s "can't even be stated" is too strong.
But see probe 4.

**Probe 3: using the lemma for `mapIn`.** With `bindAt := Effect.bind`
(unapplied, checked against a concrete type, which avoids the problem of
probe 1), the lemma `runPureBindAt` checks. Using it for
`runPureNo (mapIn f xs) = List.map f xs` fails: the instance's left side
comes out as `Cons (f x) (runPure (mapIn … xs))`, already reduced, so it
can't match the goal `runPure (bind (mapIn … xs) …)` **[checked]**.

**Probe 4: why.** `stuckComp: List a -> Comp NoOp NoRes Nat` is defined by
cases, so `stuckComp xs` is stuck for a variable `xs`. Yet
`(xs: List Nat) -> isDone (stuckComp xs) = True := xs => rfl` checks
**[checked]**, where `isDone` tests for `Done`. This can only hold if the
argument was elaborated as `Done (runPure (stuckComp xs))`. So **at the
empty row, an argument that is a computation is run in place and
re-wrapped even when the parameter's type is a `Comp`**. Every lemma about
a stuck computation becomes useless at its use sites. This is the precise
gap behind errors.md's "no proof can take apart a computation".

**Probe 5: design C in today's language.** A row type `Row = Empty | Ops op
res`, a computation type `CompR: Row -> Type -> Type` with `CompR Empty a =
a` and `CompR (Ops op res) a = Comp op res a`, and `doneR`, `bindR` defined
by cases *on the row*. `mapR row f`, written the way the elaborator would
write `mapIn`, satisfies **[checked]**:

```
theorem mapREmpty [a b: Type] (f: a -> b): (xs: List a) -> mapR Empty f xs = List.map f xs
  | Nil => rfl
  | Cons x xs => Eq.cong (Cons (f x)) (mapREmpty f xs)

theorem lengthMapR [a b: Type] (f: a -> b): (xs: List a) -> List.length (mapR Empty f xs) = List.length xs
  | Nil => rfl
  | Cons x xs => Eq.cong Succ (lengthMapR f xs)

theorem mapRCons [a b: Type] (f: a -> b) (x: a) (xs: List a):
    mapR Empty f (Cons x xs) = Cons (f x) (mapR Empty f xs) := rfl
```

These are word for word the proofs of the pure lemmas. No kernel change, no
bridging lemma.

**Probe 6: generated JS.** `stitchwort build --js` for `List.map double`,
`List.mapIn double` and `mapR Empty double` **[checked]**:

- `map` is a `for (;;)` loop that fills each cell's tail.
- `mapIn` is `runPure(mapIn({ tag: "MkSig" })(x => ({ tag: "Done", value:
  double(x) }))(xs))`; the body calls `bind((f)(x))(v7 => bind(mapIn(…)(xs))(…))`.
  The row is passed at runtime as an erased `{ tag: "MkSig" }`.
- `mapR Empty` passes `{ tag: "Empty" }` and dispatches with a `switch` in
  `bindR` and `doneR`; no loop.

**Probe 7: timings.** Node 22.23.3, averaged after a warm-up, on the
internal list representation, so no boundary encoding (bench sources in
Appendix A). "Specialised" is what design E would emit for the folded
`map`: after `Done v → v`, `bind c k → k c` and beta reduction, `mapIn`'s body
is `Cons (f x) (mapIn f xs)`, which the TRMC pass compiles to the same loop
as `map`. "Direct + yield check" is a hand-written Koka-style loop that
tests each callback result for a yield marker.

| n | `map` | `mapIn`, pure callback | specialised | direct + yield check | `mapR Empty` |
|---|---|---|---|---|---|
| 1,000 | 0.08 ms | 0.21 ms | (= `map`) | 0.04 ms | 0.53 ms |
| 10,000 | 0.18 ms | stack overflow | 0.08 ms | 0.15 ms | overflow (from 5,000) |
| 100,000 | 1.7 ms | stack overflow | 3.0 ms | 2.9 ms | overflow |
| 1,000,000 | 60 ms | stack overflow | 77 ms | 84 ms | overflow |

The "specialised" column runs the same function as `map`; the spread
between those two columns is measurement noise (garbage collection), which
bounds what these numbers can show. The yield check costs little. Note that
`effectful-map.md` measured through the exported function (with decoding
and encoding), so its absolute numbers are larger; the overflow at 10,000
agrees **[checked]**.

A callback that really suspends: `Counter.number (() => List.mapIn (x =>
x + Counter.next()) numbers) 0`, with a state-passing handler **[checked]**:

| n | JS (export) | native `stitchwort run` (whole run) |
|---|---|---|
| 1,000 | 68 ms | |
| 2,000 | 306 ms | 0.31 s |
| 4,000 | stack overflow | 0.91 s |
| 8,000 | stack overflow | 3.5 s |
| 16,000 | | 14.0 s |
| 32,000 | | 62.5 s |

Doubling `n` multiplies the time by about 4: quadratic. The cause
**[inferred]** from `bind`'s definition: element `i`'s `Call` surfaces
through `i` nested `bind`s (`bind (Call o rest) k = Call o (y => bind (rest
y) k)`), and each resumption rebuilds them. Native `stitchwort run` of
`mapIn` with a pure callback on 1,000,000 elements works (0.48 s, against
0.29 s for `map`, both including checking), because the runtime has its own
stack **[checked]**.

Probes 8 to 11 were added for the revision, on `main` at `2934c86e`.

**Probe 8: even a variable is run in place.** With probe 4's `isDone`,
`(c: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> isDone c = True := c =>
rfl` checks, for an arbitrary `c` **[checked]**. So does the same through
an identity function on computations. And `Effect.runPure (identityComp
(Done n))` is refused: "expected `Nat`, but this has type `Comp (?0 n) (?1
n) Nat`" at `Done n`, because the argument of `runPure` was itself run in
place **[checked]**. The cause: whether an expression "performs" is decided
by `may_perform` from the argument alone. A variable or call whose own type
reaches a `Comp` performs (`effects.rs:1023-1053`, `performs_after` at
`effects.rs:1109-1115`), and the parameter type it is passed to is never
consulted. A whole expression that performs, checked against a plain type,
is elaborated in the empty row and run (`check.rs:1615-1616`,
`effects.rs:2145-2160`) **[checked]**.

**Probe 9: rows are ordinary terms today.** Each of these checks
**[checked]**:

- `List.mapIn [e := Effect.Sig.MkSig Effect.NoOp Effect.NoRes] (x => x + 1)
  xs`: a program builds the empty signature and supplies it by hand, with a
  named implicit argument.
- `def leak (f: Nat -> {e} Nat): Effect.Sig := e`: a row variable is a term
  that can be returned.
- A function `inspect: Effect.Sig -> Bool` defined by matching `MkSig op
  res`, applied to a row variable.

Parametricity (an effect-polymorphic function can't behave differently
depending on its row) holds today only because `Sig` has one constructor
and a program can't take a `Type` apart. Under design C, `Row` has two
constructors, so the same freedom would let a program test for `Empty`.
Storing a row in ordinary data is already refused: `List Effect.Sig` is
`E-UNIVERSE`, since `Sig` is in `Type 1` **[checked]**.

**Probe 10: abilities live in `Type 0`.** `ability Gen where gen: Type ->
{Gen} Nat` is refused: "field `x` is too large for `Gen`: its type is in
`Type 1`, but `Gen` is in `Type`" **[checked]**. `Comp`'s parameters are all
`Type` (`Effect.sw:12`), and an effectful function's result must be in
`Type 0` (`effects.rs:887-893`) **[checked]**.

**Probe 11: an unsolved row is an error today.** A local
`let unused := List.mapIn (x => x + 1)` whose row nothing determines is
`E-UNSOLVED` ("can't work out an implicit argument") **[checked]**. There is
no row defaulting today. In practice rows are solved by the effect
machinery's own row comparison (`solve_tail`, `effects.rs:382-413`), not by
the general unifier, and a pure context solves an open row with the empty
one when it runs the call in place **[checked]** for `solve_tail`,
**[inferred]** for which path solves it in each case.

## 5. Candidate designs

Each design is judged on: proofs (do the 78 `map` statements go through
unchanged; can effectful lemmas be stated), pure-case speed (JS and
native), kernel trust, content hashing, totality, elaborator complexity and
migration cost.

### Prerequisite for every design: pass computations where computations are expected (stage 0)

Probe 4 shows that no lemma about a stuck computation can be used today.
The fix is one elaboration rule: **at the empty row, an argument whose
expected type is a `Comp` (after instantiation, metas allowed in its
arguments) is elaborated as a computation and passed, not run in place**.
D1055 keeps applying where a plain value is expected. The kernel is
unaffected: it sees an ordinary application.

With it, the library can state and prove, in `core/Effect.sw`:

```
theorem Effect.runPureBind [a b: Type]:
    (computation: Comp NoOp NoRes a) -> (next: a -> Comp NoOp NoRes b) ->
    runPure (bind computation next) = runPure (next (runPure computation))
  | Done x, next => rfl
  | Call () rest, next
```

and the fusion law handlers need, `foldComp done call (bind c k) =
foldComp (x => foldComp done call (k x)) call c` by induction on `c`
**[inferred]**: the statement is ordinary once `c` is passed. Then
`List.mapInPure: runPure (mapIn f xs) = map f xs` follows by
`Eq.trans (runPureBind …) (Eq.cong (Cons (f x)) ih)`, and errors.md's
`Fail.toResultMapIn` becomes provable. Probe 3 is this proof, failing only
because of probe 4 **[checked]** for the failure, **[inferred]** for the
fix.

Risk: some existing code might rely on a computation argument being run.
The run-in-place rule was added for operands of `=`, arithmetic and
arguments whose parameter is a plain type (abilities.md:263), so a `Comp`
parameter at the empty row should be rare outside `Effect.sw` itself
**[inferred]**.

Where the fix goes. Probe 8 shows the decision is made by `may_perform`
judging each argument by its own type (`effects.rs:1023-1053`). The rule has
to be applied in every place that decides to run something in place, not
only in direct arguments, or run-in-place will come back through another
path. The paths, all **[checked]** to exist, the classification **[inferred]**:

| Path | Where | What stage 0 does |
|---|---|---|
| Direct argument of a call | `call_performs`, `effects.rs:1030-1034` | skip an argument whose parameter type is a `Comp` |
| Piped argument, `c \|> isDone` | `may_perform`, `Expr::Pipe`, `effects.rs:978-985` | the same, for the piped value |
| Dot call, `c.isDone` | `dot_performs`, `effects.rs:1057-1067` | the receiver is the first argument: the same |
| Arguments run first inside computation mode | `run_first`, `effects.rs:1738` | the same |
| Fields of a constructor, record, tuple or list whose field type is a `Comp` | `may_perform`, `effects.rs:1009-1017`; `comp_compound`, `effects.rs:1794` | the same, per field |
| A body whose declared type is `Comp NoOp NoRes a` | `check_inner`, `check.rs:1609-1613`, then `in_place`, `effects.rs:1489` | a value whose type is already the expected `Comp` is used as it is, not rebuilt as `bind c Done` or run |

The acceptance test is observational, as the reviewer asked: a function
that explicitly takes a `Comp NoOp NoRes a` must see exactly what it is
given. With

```
def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done value => True
  | Call () rest
```

the following must hold, for each path in the table (direct, piped, dot,
inside a constructor, through an identity function):

- `isDone (Done 3) = True := rfl` checks: a written `Done` is seen as
  `Done`.
- `(computation: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> isDone
  computation = True := computation => rfl` is refused: an arbitrary
  computation is not known to be `Done` (it checks today, probe 8).
- Probe 4's `isDone (stuckComp xs) = True` for a variable `xs` is refused,
  and `isDone (stuckComp Nil) = True := rfl` checks: the computation is
  passed, and it reduces as its own definition says.
- `Effect.runPure (identityComp (Done n))` checks (it is refused today,
  probe 8).

These tests stay in the suite after stage 0, so a later change that
re-introduces run-in-place through any path fails them.

### A. Status quo: two functions plus a proved bridge

Keep pure `map` and effectful `mapIn`, and prove `mapInPure` for each pair
after stage 0.

- Proofs: pure lemmas untouched. Lemmas about effectful uses are statable
  after stage 0. Each pair needs one bridging lemma.
- Speed: pure `map` as today. `mapIn` with a pure callback still builds
  trees; users must pick the right name.
- Kernel, hashing, totality: no change. Two definitions, two hashes.
- Elaborator: stage 0 only.
- Migration: none. Cost grows with every pair: the library would have about
  70 `…In` twins if it followed Unison.
- This is what Lean does (§3.2). It does not meet the owner's "one function
  per operation".

### B. A kernel rule: `runPure (bind c k)` reduces at `NoOp` (rejected)

**Rejected unless design C proves infeasible for reasons much stronger
than implementation cost.** The analysis below is kept for the record. The
deciding argument, from the review: the rule fires for a neutral `c` and
stops being justified after substitution. Definitional equality is
infrastructure that elaboration, conversion, normalisation and proofs all
use, and its answer would depend on whether reduction happened before or
after substitution. That is a bad trade for saving elaborator work in a
small kernel. C puts the complexity in ordinary terms and the elaborator
instead.

Add to the kernel's evaluator: `runPure (bind [NoOp] [NoRes] c k) ⟶
runPure (k (runPure c))` when `c` is neutral (stuck), and keep `bind`'s own
rules when `c` is `Done` or `Call`.

- Proofs: with `map` folded, a statement `List.length (List.map f xs)`
  elaborates (D1055) to `length (runPure (map (x => Done (f x)) xs))`. Its
  `Cons` case unfolds to `runPure (bind (map … xs) (ys => Done (Cons (f x)
  ys)))`, which the rule takes to `Cons (f x) (runPure (map … xs))`, so
  `Eq.cong` proofs go through **[inferred]**, consistent with
  effectful-map.md's guess. But it is a rule about `runPure` *outside*
  `bind`; a `bind` that isn't directly under `runPure` (inside a lambda, or
  in a `foldComp`) doesn't reduce. Lemmas about pure uses that go through a
  handler won't benefit **[inferred]**.
- Soundness: every closed `c: Comp NoOp NoRes a` is `Done (runPure c)`, by
  induction (the `Call` case is absurd). So the equation is provable for all
  `c` (stage 0's `runPureBind`), and adding a provable equation as a
  conversion rule keeps the theory consistent: extensional type theory
  validates it **[inferred]**. What needs care:
  - *Confluence on open terms.* Under a hypothesis `o: NoOp` (an
    inconsistent context), `c := Call o rest` makes the two sides
    different normal forms: `runPure (Call o …)` and `runPure (k (runPure
    (Call o rest)))`. Restricting the rule to neutral `c` avoids the
    overlap, but the rule is then not stable under substitution: reduce
    first with `c` a variable, substitute `Call o rest` later, and you get
    a term not convertible with the other order. This only arises in
    absurd contexts, where any equation is provable, so it is a loss of
    completeness of conversion, not of soundness **[inferred]**. Lean lives
    with similar non-transitivity of definitional equality from proof
    irrelevance and structure eta **[unverified]**.
  - *Termination.* The rule removes a `bind`, so it can't loop with
    `bind`'s rules **[inferred]**.
  - *Trust.* It is a new kernel rule keyed on two prelude definitions
    (`Builtin::Bind`, `Builtin::RunPure`, `crates/core/src/registry.rs:332,353`).
    The kernel has no rule of this kind today; its conversion knows only
    beta, function eta and unfolding (`crates/core/src/value.rs:1966-2055`)
    **[checked]**. DESIGN.md principle 4 asks for a small kernel.
- Speed: no change. Needs design E as well.
- Hashing: one definition for `map`; the rule is part of the kernel, not
  hashed.
- Migration: hashes of `map` and dependants change; source of the 78
  statements unchanged if the rule covers them all **[inferred]**.

### C. Row-indexed computation type (recommended)

Make the empty row a separate *value* of the row type, and define the
computation type and its operations by cases on the row:

```
type Effect.Row: Type 1 =
  | Empty
  | Ops (op: Type) (res: op -> Type)

def Effect.CompIn: Row -> Type -> Type
  | Empty, a => a
  | Ops op res, a => Comp op res a

def Effect.doneIn [a: Type]: (row: Row) -> a -> CompIn row a
  | Empty, value => value
  | Ops op res, value => Done value

def Effect.bindIn [a b: Type]: (row: Row) -> CompIn row a -> (a -> CompIn row b) -> CompIn row b
  | Empty, computation, next => next computation
  | Ops op res, computation, next => bind computation next
```

A row variable `e` ranges over `Row`. A function type `a -> {e} b` with a
bare row variable is `a -> CompIn e b`. Rows with at least one ability stay
exactly as today: `{A | e}` is `Comp (Plus (ops A) (rowOp e)) …`, where
`rowOp Empty = NoOp` and `rowOp (Ops op res) = op`. A closed row with
abilities stays a plain `Comp`. Only the bare `{e}` changes.

The elaborator writes `doneIn e`, `bindIn e` and a lifting function
`liftIn e: CompIn e a -> Comp (Plus … (rowOp e)) …` (cases on `e`: `Done`
at `Empty`, `translate` at `Ops`) wherever it writes `Done`, `bind` and
`translate` for a bare row variable today. A handler whose remaining row is
`{e}` ends with the converse `lowerIn e` (`runPure` at `Empty`, the
identity at `Ops`).

Why it works: `bind` now asks about the row, and the row is known at every
pure use. `map Empty f (Cons x xs)` reduces, by `bindIn Empty`'s first
clause, to `Cons (f x) (map Empty f xs)` with `xs` a variable (probe 5's
`mapRCons` by `rfl`).

- Proofs: the 78 statements keep their source. `List.map f xs` with a pure
  `f` elaborates to `List.map Empty f xs`, which unfolds exactly as today's
  pure `map` does, so the existing proofs check unchanged (probe 5)
  **[checked]** for `map`, `lengthMap` and a `Cons` step; **[inferred]** for
  all 78. Lemmas about effectful uses: at a concrete row they are lemmas
  about `Comp` and need stage 0 and the fusion lemmas, as in every design.
  Lemmas for *every* row are statable over `CompIn e`, and are proved by
  cases on `e`.
- D1055 and SW-393 become definitional. A call at the empty row returns
  `CompIn Empty a`, which *is* `a`: no `runPure` is inserted. A pure
  callback is wrapped as `x => doneIn e (f x)`, which at `Empty` is
  `x => f x`, and that equals `f` by the kernel's function eta
  (`value.rs:1966`) **[checked]** for eta.
- Kernel: no change. `Row`, `CompIn`, `doneIn`, `bindIn` are ordinary
  prelude definitions re-checked by the kernel. `CompIn` is a large
  elimination into `Type`, as `Effect.sigOp` already is
  (`Effect.sw:104-112`) **[checked]**.
- Totality and termination: unchanged; `map` is still structural on the
  list. `Partial` rows stay as they are (they use `Delay`, not `Comp`); a
  third `Row` constructor for partial rows could come later (D1121).
- Hashing: one definition of `map`, hashed once, with a `Row` parameter.
  Every dependant's hash moves once. Hash stability is not a goal while
  there are no users.
- Unification: `CompIn ?e B` against a type `T` can't be inverted in
  general. The elaborator needs an apartness rule, a postponement path and
  a separate defaulting step. They replace the SW-393 coercion for the
  bare-row case. §5.C.1.
- Two spellings of "empty": `Empty` and `Ops NoOp NoRes` would both be
  values of `Row`, with different representations and different
  definitional behaviour. `Row` is therefore a library-internal index that
  programs can't construct or inspect, and the elaborator keeps rows in a
  canonical form. §5.C.2.
- Universes: `Row: Type 1`, which assumes abilities stay in `Type 0`.
  §5.C.3.
- Speed: by itself, no better than today: the generated code dispatches on
  the row at runtime and isn't a loop (probe 6, and `mapR Empty` overflows at
  5,000 in probe 7). It needs design E. But E becomes simple: the row is a
  constructor argument, and specialising on a known constructor and inlining
  the non-recursive `bindIn` and `doneIn` is plain partial evaluation, with
  no knowledge of effects in the backend.
- Elaborator complexity: the main cost. `effects.rs` is 2,605 lines and
  builds `Comp` types in many places; each place that can meet a bare row
  variable must use the `…In` forms. Rows with abilities are unchanged.
- Migration: change `map`'s signature to `mapIn`'s, delete `mapIn`, rename
  its callers (listed in effectful-map.md "Follow-ups"). No proof edits
  expected.

What could break **[inferred]**: code that pattern-matches on a computation
of a bare row variable's type (there is none in std: `mapIn` and the
handlers only sequence); `examples/` that print elaborated terms or types
containing `Comp` for a bare row; and the `Sig` value passed at runtime (it
becomes a `Row`, whose tag the backends must keep).

#### C.1 Inferring the row: apartness, postponement, defaulting

This replaces the first version's rule "if `T`'s head is not `Comp`, solve
`?e := Empty`". That rule was too eager: a type such as `F ?x`, a definition
stuck on an unknown, isn't visibly a `Comp` now but may become one once
`?x` is solved.

**The problem.** The elaborator meets `CompIn ?e B ≟ T` when a callback or a
call's result is compared with what its context expects. `?e` is the row of
a row-polymorphic function's use; `B` is often unknown too. Two facts drive
the rule:

- `CompIn Empty B` *is* `B`. So `?e := Empty, B := T` is a solution for
  *every* `T`. Picking it is never ill typed; the question is only whether
  it is the *only* solution.
- `CompIn (Ops op res) B` is `Comp op res B`. So another solution exists
  exactly when `T` is, or may become, a `Comp`.

Hence the principle, the same one GHC uses for closed type families
([GHC user's guide](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/type_families.html):
GHC "will select an equation only when it is sure that no incompatible
previous equation will ever apply"): **choose `Empty` only when `T` is
rigidly apart from `Comp`**, meaning no solution of the unknowns and no
reduction can turn it into a `Comp`.

**What "rigid" and "blocked" mean in Stitchwort's values.** Types are
`Value`s (`crates/core/src/value.rs:22-48`) **[checked]**. The rule first
puts `T` in weak head normal form with `force` (which also unfolds a
`Value::Call`, a call kept folded while gluing, and substitutes solved
unknowns), and unfolds a dictionary left folded by name (`unfold_folded`),
as the unifier does (`unify.rs:72-91`) **[checked]**. Then it looks at the
head:

| Head of `T` after forcing | Class | Why |
|---|---|---|
| `Value::Data(d, …)` with `d` not `Comp` (`Nat`, `List a`, records, `Vec`, interface dictionaries) | apart | a data type never reduces; records and dictionaries are data types (a record is "a data type with one constructor", `records.rs:1-4`; an interface is a record, `interfaces.rs:3-4`) **[checked]** |
| `Value::Pi` (a function type), `Value::Sort`, `Value::Eq` | apart | already in normal form; never a `Comp` |
| `Value::Neutral(Head::Def(d), …)` for an opaque primitive such as `Effect.Delay` | apart | it has no body, so it never reduces (`docs/core.md:14`) **[checked]** |
| `Value::Neutral(Head::Quot(_), …)` (`Quot A R`) | apart | a quotient type is a value (`value.rs:76-83`) **[checked]** |
| `Value::Neutral(Head::Var(x), …)` (a type variable of the definition, or one applied to arguments) | apart, for this definition | see below |
| `Value::Data(Comp, [op, res, A])` | rigid `Comp` | the D1124 rule below |
| `Value::Neutral(Head::Meta(m), …)`, a bare unknown `?T` | not a row constraint | the ordinary unifier solves `?T := CompIn ?e B` (`unify.rs:194-197`) **[checked]**, the most general answer; `?e` stays open |
| `Value::Neutral(Head::Def(d), …)` stuck on an unsolved unknown (`F ?x`) | blocked | postpone |
| `Value::Neutral(Head::Def(d), …)` stuck on a variable (`F x`) | blocked | postpone; defaulting may settle it |
| `CompIn ?f C`, the same definition stuck on another row unknown | same head | the unifier's spine rule gives `?e := ?f, B := C` |

Three choices in that table need a word.

*Type variables are apart.* A variable such as `a` in `[a: Type]` can't be
solved while this definition is elaborated: it is rigid here
(`interfaces.rs:1297-1301` already treats distinct bare variables as
rigidly distinct) **[checked]**. A caller may later instantiate `a` with a
`Comp` type, but the elaborated body `CompIn Empty a` is just `a`, so it
stays well typed after any instantiation. Inside the definition `a` is
opaque, as a type variable is in any polymorphic language. The reviewer's
"any future substitution" is about unknowns (metavariables), not about the
definition's own parameters **[inferred]**.

*The spine rule is an approximation.* `CompIn` is not injective:
`CompIn Empty (Comp op res C)` equals `CompIn (Ops op res) C`. The unifier
already compares two stuck calls of the same definition by their arguments
(`unify.rs:210-220`, "the spines must match") **[checked]**, for every
definition, and C inherits that. Two uses that share a row unknown are
nearly always meant to share the row **[inferred]**. Postponing instead is
the fallback if this ever picks wrongly.

*A definition stuck on a variable is blocked, not apart.* Unlike a bare
type variable, `F x` is a case tree waiting for `x`, and some of its
branches may be `Comp` types. Inside this definition it never reduces, so
`Empty` is a correct answer, but whether it is the intended one depends on
the branches. The rule postpones it, and defaulting picks `Empty` if
nothing else decides. Looking into the case tree's leaves, and calling `F
x` apart when none of them can be a `Comp`, is a possible later refinement.

How "stuck on an unknown" is told apart from "stuck on a variable": the
instance search already does it. `unsolved_in` finds an unsolved unknown in
a value (`interfaces.rs:1331-1340`), and `refresh` re-evaluates a value
after unknowns were solved, so a definition that was stuck takes its step
(`interfaces.rs:1322-1328`) **[checked]**. The instance search's
three-valued comparison (equal, rigidly distinct, blocked) and its
`rigidly_distinct` (`interfaces.rs:1243-1319`) are close to the apartness
test needed here **[checked]**; stage 1 should share that code.

**The rule.**

```text
CompIn ?e B ≟ T
  1. Force T (and unfold a folded dictionary).
  2. T apart from Comp:           ?e := Empty, then B ≟ T.
  3. T = Comp op res A (rigid):   the D1124 rule.
  4. T a bare unknown:            ordinary unification (?T := CompIn ?e B).
  5. T blocked:                   postpone the constraint.
```

The same rule applies in the other direction (`T ≟ CompIn ?e B`), which is
SW-393's case: a pure function passed where `a -> {e} b` is expected.

**The rigid-`Comp` case (D1124).** Here both `?e := Ops op res, B := A` and
`?e := Empty, B := Comp op res A` are well typed, so unification alone
can't choose. The elaborator chooses by what a `Comp` means in source:

- `op` headed by `Plus` (the translation of a row with at least one
  ability, `effects.rs:178-235`) **[checked]**: `?e := Ops op res, B := A`.
  The callback is effectful and the function becomes effectful. This is
  today's behaviour, where `{e}` against `{IO}` solves `e` with `IO`
  (`solve_tail`, `effects.rs:382-413`) **[checked]**, and Unison's.
- `op` is `NoOp`: `Comp NoOp NoRes A` only appears under C when written out
  by hand, which is asking for the tree as data (stage 0's tests are an
  example). So `?e := Empty, B := Comp NoOp NoRes A`. This also keeps the
  canonical form (§5.C.2): the elaborator never makes `Ops NoOp NoRes`.
- `op` blocked: postpone.

This is the one place where the elaborator picks one solution among
several, and it is documented as a convention, not presented as
unification.

**Where the rule lives and how postponement works.** The unifier has no
constraint store: `unify` answers yes or no, and a no may be followed by
trying another way (`unify.rs:15-23`) **[checked]**. Postponement exists in
the elaborator in three narrower forms today **[checked]**:

1. a lambda argument whose parameter type isn't known yet is checked after
   the later arguments (`check.rs:1051-1170`);
2. auto arguments and instances are recorded as obligations and solved
   once the declaration is elaborated, in rounds that repeat while a round
   makes progress (`auto.rs:62-99`, called from `finish`, `lib.rs:831-834`);
3. a mismatch is retried after ready instances are found, and then through
   the effect coercions (`check.rs:2185-2205`).

So stage 1 splits the rule in two **[inferred]**:

- Steps 2 to 4 are a new case in `unify_step`. Solving `?e := Empty` and
  pushing `B ≟ T` is ordinary unification, safe wherever `unify` is
  called.
- Step 5 returns "no" from `unify`. The mismatch fallback in
  `check.rs:2185-2205`, where `effects::coerce` is called today, records a
  *row constraint* (its context, the found and expected types, the span)
  next to the obligations, and accepts the term as it is. The term is well
  typed once the constraint is solved. Row constraints are retried in the
  same rounds as obligations, after `refresh`; one that is solved counts as
  progress. Anything still unsolved at the end is an error, so nothing
  unchecked reaches the kernel, which re-checks the final term anyway.

Does the elaborator need `?e` early, before the rounds? Mostly not
**[inferred]**: a callback body checked against `CompIn ?e B` can be
elaborated with `doneIn ?e` and `bindIn ?e`, which are correct for any
row. If the body performs an ability, that already forces `?e` to be
non-empty, and today's `extend` (`effects.rs:683-695`) **[checked]** does
the same job: it solves the open row with the ability and a fresh tail.

**Defaulting is a separate step.** When the rounds stop making progress,
and before errors are reported, each remaining row unknown that is
*eligible* is set to `Empty`, and the rounds resume (a solved row can
unblock instances). Eligible means:

1. its type is `Row`, and it was made by instantiating a row-polymorphic
   function's implicit row parameter (a definition's own row variables are
   variables, not unknowns, and are never defaulted);
2. no constraint or obligation made progress in the last round;
3. no ability was performed against it (that would have solved it
   already).

Defaulting can't make a term ill typed, since `Empty` solves every
`CompIn ?e B ≟ T`. What it can do is pick the pure reading where an
effectful one was meant; that shows up as a type error at the effectful
use, which gets a note saying the row defaulted to pure, as a defaulted
number literal gets one today (`Defaulted`, `numbers.rs:28-35`, used by
`explain_default`, `numbers.rs:441-460`) **[checked]**.

Stitchwort has no defaulting step after solving today. Number literals
default eagerly, at the literal (`numbers.rs:291-312`), with one retry that
checks literals last (`check.rs:1024-1048`) **[checked]**. Row defaulting
can't be eager, because a row is often settled by something checked later,
so it uses the end-of-declaration rounds instead.

**Worked examples.** For a call written as the elaborator sees it,
`List.map [e := ?e] callback xs` (after the fold, stage 3), where `map`'s
parameter is `(f: a -> {e} b)`, so the callback's expected type is
`a -> CompIn ?e ?b`.

| Callback or context type `T` | Class | Result |
|---|---|---|
| `Nat` (a callback `f: Text -> Nat`) | apart | `?e := Empty`, `?b := Nat`; `map` is pure here |
| `List a` | apart | `?e := Empty`, `?b := List a` |
| `Nat -> Text` (a callback returning functions) | apart | `?e := Empty`, `?b := Nat -> Text` |
| `Point`, a record | apart | `?e := Empty`, `?b := Point` |
| `?T` (a callback whose result type isn't known yet) | bare unknown | `?T := CompIn ?e ?b`; `?e` is decided later, or defaulted |
| `F ?x`, see below | blocked, then rigid `Comp` | postponed; effectful once `?x` is solved |
| `Comp (Plus IO NoOp) IO.res Nat` (a callback `f: Text -> {IO} Nat`) | rigid `Comp`, `Plus` | `?e := Ops (Plus IO NoOp) IO.res`, `?b := Nat` |
| `Vec Nat 3`, against `CompIn ?e (Vec ?b ?n)` (`Vec.map`, a dependent result type) | apart | `?e := Empty`, then `?b := Nat`, `?n := 3` |
| `Cell ?i` (a type family applied to an unknown index) | blocked | postponed; decided when `?i` is |
| `CompIn ?f c` (the callback is itself row-polymorphic) | same head | `?e := ?f`, `?b := c` |

The `F ?x` case is the one the old rule got wrong. With

```
def Answer: Bool -> Type
  | True => Effect.Comp (Effect.Plus Log Effect.NoOp) Log.res Nat
  | False => Nat
```

and a callback of type `Text -> Answer ?x`, where `?x` is fixed by a later
argument to be `True`: the old rule saw a head that isn't `Comp`, chose
`?e := Empty` and `?b := Answer ?x`, and `map` became pure, returning a list
of unrun `Log` computations. Under the new rule the constraint waits; once
`?x := True`, `Answer True` reduces to a `Comp` over `Plus`, and `map`
becomes effectful in `Log`, as it would with a callback written
`Text -> {Log} Nat` **[inferred]**.

A dependent result type that stays stuck on a variable: with
`Vec.tabulate`-style `(index: Fin n) -> {e} Cell index` and `Cell` defined
by cases on the index, `Cell index` for the bound variable `index` is
stuck on a variable, so it is postponed, nothing else decides it, and
defaulting picks `Empty`. The result `CompIn Empty (Cell index)` is
`Cell index`, correct for every `index` **[inferred]**.

Today's code has the weakness the reviewer pointed out, in a smaller form:
SW-393's coercion refuses only when the pure function's result type is a
bare unknown (`effects.rs:2571-2581`), so a result type stuck on an unknown
passes that guard **[checked]** for the guard, **[inferred]** that it can
misfire. Stage 1 replaces that path with the rule above.

#### C.2 `Row` as a library-internal index

The review's point: `CompIn Empty a` is `a`, while `CompIn (Ops NoOp
NoRes) a` is a tree. Two semantically equal rows would have different
representations and different definitional behaviour. That is tolerable
only if programs can't make, inspect or compare rows. Otherwise an
"effect-polymorphic" function could test whether its row is `Empty` and
behave differently, and effect polymorphism would stop being parametric.

Probe 9 shows that today a program *can* build a row (`MkSig NoOp NoRes`),
supply it by hand, return it, and match on it. It does no harm today only
because `Sig` has one constructor. Under C it would.

**The boundary.**

- `Row`, its constructors `Empty` and `Ops`, and the functions that take a
  row apart (`CompIn`, `doneIn`, `bindIn`, `liftIn`, `lowerIn`, `rowOp`,
  `rowRes`) can be *named* only in the standard library. A program that
  names one gets an error (`E-INTERNAL`, say). Std's own lemmas about
  `CompIn e` for every row still need to name `Empty` and `Ops`, which is
  why "only the library" rather than "only `Effect.sw`".
- A program still gets row variables through `{e}` in types, and may pass
  one on (`[e := e]`). It can't take one apart (the constructors can't be
  named, and a match with only a wildcard reveals nothing), can't build
  `Ops NoOp NoRes`, and can't store a row in ordinary data, because `Row`
  is in `Type 1` and `List`, `Option` and records hold `Type 0` values
  (probe 9's `List Effect.Sig` is refused) **[checked]** for `Sig`,
  **[inferred]** for `Row`. There is no `DecEq Row`, so rows can't be
  compared.
- Printed types show `{e} b`, not `CompIn e b`.

**Enforcement, cheapest first** (D1122):

- Today there's no visibility control at all: "Visibility of declarations:
  everything" (`docs/proposals/multi-file.md:498`) **[checked]**. SW-150
  (file-private declarations) is in the backlog and is about one file, which
  is too narrow here: the row's constructors are needed in `Effect.sw` and in
  every std file whose lemmas quantify over rows **[checked]** for the
  ticket's scope.
- `Sig` and `sigOp` aren't protected today (probe 9). The `RESERVED` list
  (`lib.rs:143-152`) stops names from being *redefined*, not used
  **[checked]**.
- The compiler already makes names that source can't spell: `%unit`
  (`lib.rs:137-139`) and an interface's hidden projections `Pretty.%f`
  (`interfaces.rs:8-10`); `%` is an operator token, so no source file can
  declare or name them (`crates/syntax/src/lexer.rs:583`) **[checked]**. But
  then std's lemmas couldn't name them either.
- The elaborator already knows whether a file is part of the library (a
  program can't add to `Std`, `scope.rs:529-535`; library tests are marked,
  `lib.rs:179`) **[checked]**.

So the cheapest enforcement that keeps std's proofs is a library-only name
check: the internal declarations are listed (an attribute such as
`@[internal]`, or a short list in the compiler, as `RESERVED` is), and name
resolution refuses them outside std **[inferred]**. Later, SW-150's `private`
could become the general form of the same check.

**Canonical form.** The invariant: *a row with no abilities and no row
variable is always `Empty`*. The elaborator's row translation (`ops`,
`res`, `comp_type`, `effects.rs:178-235`) is the one place rows become
terms **[checked]**; under C it writes `Empty` for the empty row, the row
variable itself for a bare `{e}`, and `Ops (Plus …) …` only when there's at
least one ability. What checks it:

1. the boundary: programs can't write `Ops` at all;
2. a debug assertion in the translation function;
3. a unit test in stage 1 that `{}` and an instantiated `{e}` at `Empty`
   elaborate to plain types, with no `Comp` in the term;
4. the D1124 rule, which never solves a row with `Ops NoOp NoRes`.

The kernel doesn't check it, and doesn't need to: breaking the invariant
can't make anything unsound. It would only give slower code and pure
equations that are no longer definitional.

**Runtime data or index?** (The review's §9.) Semantically an index: with
the boundary, no program can observe a row, so a row only selects a
representation. Operationally it is still passed. Today a row is passed at
runtime as an erased `{ tag: "MkSig" }` that carries no information (probe
6) **[checked]**. Under C the tag carries one bit, `Empty` or `Ops`, and
unspecialised code dispatches on it in `bindIn` and `doneIn` (probe 6's
`mapR Empty` passes `{ tag: "Empty" }` and switches on it) **[checked]**.
The interaction with E: because only the elaborator makes rows, every row
argument at a call site is either a constructor it wrote or the enclosing
definition's own row variable. So specialising from each concrete use
reaches every call with a known constructor **[inferred]**. The exception is
a row-polymorphic function passed as an argument to a parameter whose type
quantifies over rows (rare, and only possible at `Type 1`); that call keeps
the runtime tag and dispatches, which is slower but correct. Rows can't be
erased everywhere without specialising everything, so the tag stays in
unspecialised code.

#### C.3 Universe levels

Today abilities' operations always live in `Type 0`: `Comp`'s `op`, `res`
results and `a` are `Type` (`Effect.sw:12`), an effectful function's result
must be in `Type 0` (`effects.rs:887-893`), and an operation that takes a
`Type` is refused (probe 10) **[checked]**. `Sig` is already `Type 1` for
this reason (`Effect.sw:104`) **[checked]**. So `Row: Type 1` matches the
present language.

The limitation, stated: under C, abilities whose operations mention `Type`
(or anything in `Type 1` or above) can't be used in a bare row variable.
Stitchwort has no universe polymorphism (`docs/core.md:22`; DESIGN.md:407
"No universe polymorphism at first") **[checked]**. When it comes, the
extension path is `Row u` and `CompIn u`, one per universe, rather than
fixing this representation at `Type 1`. Until then a `Type 1` copy would be
a separate declaration with its own name, as `Quot` is at `Type 0` only
(`docs/core.md:418`) **[checked]**.

### D. Lean-style proven replacement (`csimp`)

An attribute `@[replaces List.map at Empty]` on a theorem
`(f: a -> b) -> (xs: List a) -> List.map f xs = List.mapPure f xs` tells the
backends to compile the empty-row use of `map` as `mapPure`.

- Proofs: does nothing for proofs about the effect-polymorphic `map`. It
  is a pure speed device, useful with B or C. Or the reverse: keep pure `map`
  for proofs and `mapIn` for users, and let the backend run `mapIn` at the
  empty row as `map`, which needs A's bridging lemma.
- Speed: exactly today's `map` at the empty row.
- Trust: none added to the kernel; the backends are already untrusted
  (`crates/rt/src/lib.rs:1-5`), and the theorem is checked. An unproved
  `implemented_by` would only put outputs at risk, but DESIGN.md principle 3
  would require tracking it as an assumption.
- Hashing: the attribute is metadata linking two definitions; the theorem
  has its own hash.
- Cost: one hand-written twin and one theorem per function: the twins
  the owner wants to avoid, hidden from users.

### E. Backend specialisation at the empty row

**Specification.** E is generic partial evaluation, not an effect-specific
pass. The backend knows nothing about rows except that `Row` is in a fixed
list of *representation-driving* parameter types:

1. **Specialise.** For a definition called with a static constructor
   argument for a parameter whose type is in the list, make a copy with that
   argument fixed. Initially the list holds only `Row`, and only the `Empty`
   constructor is specialised on (the `Ops` constructor's fields are types,
   which are erased, so an `Ops` copy would be the generic code minus one
   tag test).
2. **Inline** small non-recursive definitions called with a static
   constructor argument (`bindIn`, `doneIn`, `liftIn`, `lowerIn` are each a
   single case on the row).
3. **Beta-reduce** and fold `case` on a known constructor.
4. **Remove dead code** (the unreachable `Ops` branches).
5. Run the **ordinary pipeline**, including TRMC.

**Test case: `map`.** Under design C, the row argument is the constructor
`Empty`. Fixing it, inlining `bindIn Empty c k` to `k c` and `doneIn Empty v`
to `v`, and beta reducing turns `map`'s body into `Cons (f x) (map_Empty f
xs)`, which the existing TRMC pass makes a loop **[inferred]**; the result
is `List.map`'s code (probe 7, "specialised"). The JS backend already
inlines helpers inside self tail loops (`SelfCall`'s `inline`,
`crates/js/src/lib.rs:1930-1934`, tried in order at `lib.rs:2170-2185`)
**[checked]**, so step 2 extends something that exists.

Under today's encoding instead, the backend would have to see that the row
argument is `MkSig NoOp NoRes`, normalise each `bind`'s implicit `op`
argument to `NoOp`, and apply type-directed rewrites (`Done v → v`,
`bind c k → k c`, `runPure → id`). Possible, since the JS backend works
from kernel terms before erasure, but it needs the kernel evaluator in the
backend and changes the runtime representation of values of type
`Comp NoOp NoRes a`, which must then never meet unspecialised code
**[inferred]**. That is the effect-specific knowledge C avoids.

**Transitive specialisation and code size.**

- Copies are made transitively from each use: a specialised function's
  calls that pass its own (now fixed) row are specialised too. A copy is
  keyed by (definition hash, row constructor), so it is made once per
  program.
- Only parameters in the list drive copies. Nothing else (types, numbers,
  functions) is specialised by this pass, so it can't grow into general
  monomorphisation by accident. Adding a type to the list is a design
  decision, not a tuning knob.
- A definition with several row parameters is specialised only when all of
  them are `Empty` (one copy); otherwise the generic code runs. So each
  row-polymorphic definition has at most one extra copy, and the generated
  code is at most about twice the reachable row-polymorphic code
  **[inferred]**.
- Inlining in step 2 is limited to non-recursive definitions below a size
  bound, and to definitions that are a single case on a static argument.

Other points:

- The native runtime (`crates/rt`) gets the same pass in its lowering; it
  shares erasure decisions with JS (`crates/rt/src/lib.rs:11`) **[checked]**.
- Hashing: copies are backend artefacts, not hashed definitions.
- Stack: specialisation removes the overflow for pure uses, because the
  copy is a loop. It does nothing for genuinely effectful uses (design F).

### F. A different runtime representation for effectful code

Keep `Comp` as the kernel's semantics; change only how the backends run
it. The kernel's tree and the runtime representation are already decoupled
(the backends are untrusted, `crates/rt/src/lib.rs:1-5`) **[checked]**, so
the architecture doesn't need to commit to one representation now.

**The requirement** for stage 4:

1. runtime sequencing makes `bind` amortised O(1);
2. resuming after an operation doesn't rebuild a chain whose length grows
   with the work done so far (probe 7's quadratic cause);
3. JS execution is stack-safe (SW-396), since JS has no tail calls;
4. pure paths keep today's speed: a computation that performs nothing
   costs little more than a direct call.

**Candidates**, to be evaluated against that requirement in stage 4's own
design note, with measurements:

- **CPS with a trampoline.** A computation is a function taking "what to do
  with the result" and "what to do with an operation"; `bind` becomes O(1)
  (codensity, Voigtländer 2008). A trampoline (a loop that runs one step at
  a time) bounds JS's stack, as Links' JS backend does (FSCD 2017).
- **A type-aligned continuation queue.** Keep `Done` and `Call` at runtime,
  but store a `Call`'s continuation as a queue of functions, so appending
  is O(1) and a resumption takes from the front (Kiselyov and Ishii 2015).
  Closer to the kernel's tree, so differential testing is simpler
  **[inferred]**.
- **Evidence or capability passing.** Handlers are passed down, and an
  operation is a lookup and a call (Koka's evidence vectors, Effekt's
  capabilities, §3.1). Tail-resumptive clauses run in place. This changes
  the most, and gives the most for state-like handlers.

Whatever is chosen, two techniques apply on top: the **bind-inlining fast
path** (compile `bind c k` as `case c of Done x -> k-body | Call … -> slow
path`, with join points so code size stays linear; recursion stays tail
recursion on the `Done` path, so TRMC applies within one function), and
**tail-resumptive handlers in place** (a clause of the form `op x k => k e`,
or for a state-passing handler `s => k v s'`, runs at the call site without
building a continuation).

The backends are untrusted, so this changes no proof. It needs
differential tests against the reference evaluator, which the rt already
has (`crates/rt/src/lib.rs:1-5`) **[checked]**.

### G. My own: one definition, two elaborations

The elaborator could elaborate a row-polymorphic definition twice: once
for all rows and once at the empty row (a pure twin with its own hash),
and pick the twin wherever the row is empty. Proofs would see the pure
twin, and its lemmas would be today's lemmas. It meets both goals without
kernel or backend work, but makes "one definition" a fiction: two hashes,
and theorems about the pure twin say nothing about the polymorphic one
unless a bridging lemma is generated and proved for each. Design C gets
the same proofs with one hash. Listed for completeness; not recommended.

### Proof tooling for effectful code (every design)

Proofs about genuinely effectful uses are proofs by monad laws, as the
interaction-trees work shows (§3.2). But Stitchwort's `Comp` is inductive,
so its laws are ordinary equalities proved by induction, with no
bisimulation (a proved "behaves the same" relation, needed for
coinductive trees). So the plan is a small algebraic library in
`core/Effect.sw`, not an interaction-trees framework:

| Lemma | Statement, informally |
|---|---|
| `Effect.bindDone` | `bind c Done = c` (right identity; `bind (Done x) k = k x` is already definitional) |
| `Effect.bindAssoc` | `bind (bind c k) h = bind c (x => bind (k x) h)` |
| `Effect.foldCompDone` | `foldComp done call (Done x) = done x` |
| `Effect.foldCompBind` | `foldComp done call (bind c k) = foldComp (x => foldComp done call (k x)) call c` (handler fusion) |
| `Effect.translateBind` | moving a computation into a larger row commutes with `bind` (naturality) |
| `Effect.runPureBind` | `runPure (bind c k) = runPure (k (runPure c))` |
| `Effect.morphismBind` | a handler that is a monad morphism (it maps `Done` to `return` and `bind` to `bind`) commutes with sequencing |

All are proved by induction on `c` **[inferred]**, and all need stage 0, so
that `c` is passed rather than run. Most effectful proofs should then be
equational rewriting or induction on `Comp`. Under design C each has a
`…In` version for every row, proved by cases on the row, where the `Empty`
case is `rfl`. An explicit equivalence relation between differently shaped
trees is added only if a proof needs it; none does today.

### Comparison

| | A | B (rejected) | C | D | E | F |
|---|---|---|---|---|---|---|
| One function per operation | no | yes | yes | yes, plus hidden twin | n/a | n/a |
| 78 `map` statements unchanged | yes (untouched) | likely | yes (probe 5) | no help | no help | no help |
| Effectful lemmas statable | after stage 0 | after stage 0 | after stage 0 | after stage 0 | n/a | n/a |
| Pure speed as today | yes | needs E | needs E | yes | yes | partly |
| Effectful speed | quadratic | quadratic | quadratic | quadratic | quadratic | linear |
| Kernel change | no | yes | no | no | no | no |
| Elaborator work | small | small | large | small | none | none |
| Backend work | none | E | E | small | medium | large |

## 6. Recommendation and staged plan

Adopt **C + E**, preceded by **stage 0**, then **F** for effectful speed.
Fold `map` once C and E are in. Extend the convention one function at a
time, when a program needs it (the board's rule that tickets need a
concrete trigger).

The main reasons: C is the only design that keeps the existing proofs as
they are without a kernel rule; it makes D1055 and SW-393 definitional
instead of special cases; and it reduces E to generic partial evaluation.
B is rejected (§5.B).

| Stage | Work | Lanes, rough cost | Acceptance |
|---|---|---|---|
| 0 | Elaborator: pass a computation where a `Comp` is expected, on every path in the stage 0 table (§5). Library: the proof-tooling lemmas that don't need C (`runPureBind`, `bindDone`, `bindAssoc`, `foldCompDone`, `foldCompBind`), `List.mapInPure`, `Fail.toResultMapIn` | 1 lane, small to medium | the observational `isDone` tests (§5 stage 0) on every path; probe 3 checks; the theorems check; targeted effect tests and `examples/accept/effect*` pass |
| 1 | Design C: `Row`, `CompIn`, `doneIn`, `bindIn`, `liftIn`, `lowerIn` in `core/Effect.sw`, library-internal (D1122); canonical rows; the elaborator uses them for bare row variables; the apartness rule, row constraints in the end-of-declaration rounds, and row defaulting (§5.C.1) | design review, then 1 to 2 lanes, large | probe 5's three theorems hold with `List.mapIn` in place of `mapR`, by the same proofs; every existing effect example and AoC day using `mapIn` checks unchanged in source; one test per row of the worked-examples table in §5.C.1, including `F ?x`; a program naming `Effect.Row.Empty` is refused; `{}` elaborates to a plain type |
| 2 | Design E in JS and rt, as generic partial evaluation (§5.E) | 1 lane per backend, medium | `map` as the test case: the JS for `List.mapIn` used at `Empty` is the same loop as `List.map` (diff of the two functions modulo names); within 10% of `map` at 1,000,000 elements; 1,000,000 elements on both backends with a pure callback; the pass contains no reference to `Comp`, `bind` or `Done` |
| 3 | Fold: `map` gets `mapIn`'s signature, `mapIn` is deleted, callers renamed | 1 lane, small | all 78 statements and their proofs check with no source change; std, AoC and examples pass; JS benchmark of `map` within 10% of today |
| 4 | Design F: its own design note starts with a close reading of the literature (Voigtländer 2008, Kiselyov and Ishii 2015, Hillerström, Lindley and Atkey 2017, Koka evidence passing, Effekt capability passing; Matt, 24 Oct 2026), evaluates the candidates (§5.F) against the requirement, then implementation in JS and rt | design note, then 1 to 2 lanes, large | `labelAll` (probe 7) on 1,000,000 elements runs on both backends; doubling `n` at most 2.5 times the time; differential tests against the reference evaluator pass |
| 5 | Further functions as needed (`foldLeft`, `filter`, `any`/`all`/`find`, `Option.map`, a new `forEach`), with `…In` versions of the proof-tooling lemmas when the first effectful proof needs them | 1 small lane each | each function's existing lemmas check unchanged |

Stages 0 and 2 are independently useful: stage 0 makes effectful lemmas
possible at all, and stage 2 speeds up today's pure uses of `mapIn` and of
handlers with open rows.

## 7. Decisions for the owner

**Decided (Matt, 24 Oct 2026):** D1116 to D1126, each as recommended below.

After stage 1, first part (Matt, 24 Oct 2026): **D1140 (a)** (= D1133): `=` operands and `if`/`match` branches whose expected type is a computation pass it as written. **D1141 (d)** (= D1134): abilities stay on arrows in the surface language (computations are passed as thunks `() -> {Fail} a`); proofs get an erased, proof-only `reify` or per-ability eliminators to case-split on a computation, so the runtime is not committed to materialised trees. See [computation-values.md](computation-values.md) and its [external review](computation-values-external-review.md); a design note for the proof-only reification comes first: [proof-reification.md](proof-reification.md). Stage R2 of that note (SW-420) makes the second half true: outside the library, `Effect.Comp`'s constructors and the definitions that match on it (`foldComp`, `bind`, `translate`, `runPure`) can be named only in erased declarations (`E-PROOF-ONLY`), so a program can no longer see a tree.

**D1142 (a)** (Matt, 24 Oct 2026, after an [external review of the row design](effect-rows-external-review.md)): programs may declare an effect-row parameter (`[e: Row]`, `type Handlers (e: Row)`) and pass it on; rows stay abstract indices: programs can't construct, inspect, compare or eliminate them (`Empty`, `Ops`, `CompIn` and the row eliminators stay library-internal).

**D1143 (a)** (Matt, 24 Oct 2026): the source name of the row type is `Effects`, not `Row` (`type Handlers (e: Effects)`, `[e: Effects]`), so it names the concept, not the representation; its constructors stay internal.

**D1160 deferred** (Matt, 24 Oct 2026): concrete effects as a type argument (`Checker {Fail}`, `{}`) are not built; a type's `Effects` parameter is only inferred from callbacks. Revisit when a real program (std or AoC), not a documentation example, needs to name such a type. Focus stays on one `List.map` that is fast, stack-safe and provable (stages 2 to 4).

After stage 0 (Matt, 24 Oct 2026): **D1133** — whether operands of `=` and `if`/`match` branches with a `Comp` expected type pass computations (stage 0 left them running in place) is settled in the stage 1 design. **D1134** — a way to write a `{Fail} b` binder type, which `Fail.toResultMapIn` (SW-378) needs, is part of the stage 1 design too.

Each decision lists its options; the recommended one is marked. D1116 to
D1121 are from the first version, with D1116 and D1119 revised after the
review. D1122 to D1126 are new.

**D1116. Direction for effect-polymorphic library functions.**
(a) Status quo: separate pure and effectful functions with a proved bridge
each (design A, as Lean does).
(b) Rejected unless (c) proves infeasible for reasons much stronger than
implementation cost: a kernel reduction rule for `runPure (bind c k)` at the
empty signature (design B).
(c) **[Recommended]** A row type with a separate empty row, and a
computation type defined by cases on it, so the empty row is the plain type
(design C), subject to the internal-row boundary (D1122) and the apartness
rule (D1123).
(d) Proven replacements for the backends only (design D).
Reason: (c) is the only option where the existing proofs check unchanged
with no new kernel rule (probe 5); (b) would make definitional equality
depend on the order of reduction and substitution.

**D1117. Pass computations where a computation is expected (stage 0).**
(a) **[Recommended]** Yes, now, whatever D1116 decides, on every path that
runs computations in place, with observational tests.
(b) No: keep running every computation argument at the empty row.
Reason: without it no lemma about a stuck computation can be used (probes 4
and 8), in any design.

**D1118. Making pure uses fast in the backends.**
(a) **[Recommended]** Specialise row-polymorphic definitions at the empty row
in JS and rt, as generic partial evaluation on a fixed list of
representation-driving parameters, initially only `Row` (design E).
(b) Dynamic dispatch only: no specialisation, accept slower pure uses.
(c) A `csimp`-style attribute with a proven twin per function (design D).
Reason: (a) restores today's loop with no twins, and under (c) of D1116 it
is ordinary partial evaluation with no knowledge of effects.

**D1119. The quadratic, stack-hungry effectful case (SW-396 and probe 7).**
(a) **[Recommended]** A later stage (stage 4) that meets a stated
requirement: `bind` amortised O(1), resumptions don't rebuild linear
chains, JS stack-safe, pure paths stay fast. Its own design note compares
CPS with a trampoline, a type-aligned continuation queue, and evidence or
capability passing, plus a bind-inlining fast path.
(b) Only a trampoline for JS stack safety; leave the quadratic time.
(c) Defer until a program is hurt by it.
Reason: an effectful `map` over 4,000 elements already fails in JS and
32,000 take a minute natively; the requirement is clear, but the best
representation needs its own measurements.

**D1120. Which functions become effect-polymorphic.**
(a) **[Recommended]** `map` first (fold `mapIn`), then others one at a time
when a program needs them.
(b) A Unison-like set at once: about 15 list, option and map functions.
(c) Every function with a callback (about 70).
Reason: each fold re-checks that function's lemmas; one at a time keeps
lanes stage-sized and follows the backlog rule.

**D1121. `Partial` rows under design C.**
(a) **[Recommended]** Leave them as they are (`Delay`); revisit when a
callback needs to be partial.
(b) Add a third `Row` constructor for partial rows now.
Reason: no current program passes a partial callback, and `Delay` has its
own runtime path.

**D1122. How `Row` is kept internal to the library.**
(a) **[Recommended]** A library-only name check: `Row`, `Empty`, `Ops` and
the functions that take a row apart can be named only in std files; a
program that names one gets an error. Programs still get row variables
through `{e}` and may pass them on.
(b) Compiler-made hidden names (`%`-names, as `%unit` and `Pretty.%f` are),
which no source file can spell, std included.
(c) Wait for file-private declarations (SW-150).
(d) Convention only: document that programs shouldn't use rows, and check
nothing.
Reason: (a) is one check in name resolution and keeps std's lemmas about
every row possible; (b) would forbid those lemmas, (c) is per file while
rows are used across std files, and (d) leaves `Ops NoOp NoRes` and
row-testing functions possible.

*Note, 24 Oct 2026 (external review follow-up, SW-406).* D1122's guarantee is
not "parametricity" in the strong sense. What it gives: code abstract over an
effects parameter can't construct, inspect, compare or branch on it. The type
theory itself computes differently at the empty row, by design (design C:
`CompIn Empty a` is `a`, `CompIn (Ops op res) a` is `Comp op res a`). In
user-facing material rows are "effect-row parameters" or "indices", not
"values". The sections above are left as written.

*Note, 24 Oct 2026: interface resolution and `CompIn e A` (SW-406, review
follow-up).* The rule: inside a definition abstract over `e`, instance
resolution must not speculate about `e`; once the row is concrete, ordinary
computation decides. This is what the resolver does, with no change
[checked]: `interfaces::attempt` looks an instance up by the data type at the
head of the goal's argument. `CompIn e A` with a rigid `e` is a stuck
definition, not a data type, so it has no instance (`E-INSTANCE-NONE`) rather
than a guessed one (`examples/reject/interfaces-comp-in-rigid-row.sw`: instances
for `Nat` and for `Comp op res a`, goal `Label (CompIn e Nat)`). With a
concrete row the type computes first: `Nat` at `Empty`, `Comp op res Nat` at a
row with abilities, and the matching instance is used; a row unknown still
undecided waits, and is the unifier's to decide (put aside, then defaulted to
`Empty`, D1123), never the resolver's (`examples/accept/interfaces-comp-in.sw`,
with tests that show which instance was chosen). Call arguments are the
other route to a goal on the result: `f ()` inside an effect-polymorphic body is
bound first, so its goal is on `A`, not `CompIn e A`.

**D1123. Inferring the row: unification and defaulting.**
(a) **[Recommended]** The apartness rule: solve `?e := Empty` only when the
other type can never become a `Comp`; postpone blocked cases as row
constraints retried in the end-of-declaration rounds; after the rounds
stall, default eligible row unknowns to `Empty`, with a note on any later
error (§5.C.1).
(b) The apartness rule with no defaulting: an undetermined row is
`E-UNSOLVED`, as today (probe 11).
(c) The first version's rule: any head that isn't visibly `Comp` gives
`Empty`.
Reason: (a) never commits early and stays convenient; (b) asks for
annotations in cases where pure is the only sensible answer; (c) picks the
wrong reading for types that become `Comp` later (the `F ?x` example).

**D1124. A callback whose type is a `Comp` (the rigid-`Comp` case).**
(a) **[Recommended]** A `Comp` over at least one ability makes the function
effectful in those abilities (`?e := Ops …`); a `Comp NoOp NoRes` written by
hand is passed as data (`?e := Empty`).
(b) Always postpone, and ask for an annotation if nothing else decides it.
(c) Always treat the `Comp` as data (`?e := Empty`).
Reason: (a) is today's behaviour and Unison's for effectful callbacks, and
it never makes the non-canonical `Ops NoOp NoRes`; (b) would need
annotations on every effectful callback, and (c) would stop `map` from
running effects.

**D1125. The universe of `Row`.**
(a) **[Recommended]** `Row: Type 1` now, with the limitation documented:
abilities whose operations mention `Type` can't be used through a bare row
variable. Move to `Row u` when universe polymorphism exists.
(b) Wait for universe polymorphism before building C.
Reason: abilities are always in `Type 0` today (probe 10), so the
limitation costs nothing now, and universe polymorphism has no date.

**D1126. Tooling for proofs about effectful code.**
(a) **[Recommended]** A small library of named algebraic lemmas about `Comp`
(`bindDone`, `bindAssoc`, `foldCompDone`, `foldCompBind`, naturality of
`translate`, `runPureBind`, a monad-morphism lemma), proved by induction;
an equivalence relation only if a proof needs one.
(b) An interaction-trees-style framework with its own equivalence relation
from the start.
Reason: `Comp` is inductive, so ordinary equality and induction suffice;
(b) adds machinery no current proof needs.

## As built (stage 0)

SW-405, 24 Oct 2026.

**The rule.** A part of an expression whose place has an `Effect.Comp` type,
whatever its row and with unknowns allowed in it, doesn't perform where it's
written: it's elaborated as a computation of its own and passed unchanged.
`effects::is_comp_type` is the test (the head is `Comp`; the row isn't
decoded). The places, and where each is handled:

| Path | Where it's decided | Where the part is kept from running |
|---|---|---|
| Direct argument (positional or named, `(x := c)`) | `call_performs` asks `passed_args`, which reads the parameter types off the head's type (`pi_slots`) or a constructor's fields (`ctor_slots`) | `comp_app` skips `run_first` for it |
| Piped argument, `c \|> f` | `may_perform`, `Expr::Pipe`, through `piped_passed` | `pipe_call`; `pipe::infer_pipe` infers it without running (`check::infer_unrun`) |
| Dot call's receiver, `c.f` | `receiver_passed`, through `dot::target_place` (the receiver's place among the target's explicit parameters) | `comp_app`, `comp_compound`; `dot::infer_receiver` in `infer_dot` and `prefix_form` |
| Constructor field by position | as a direct argument (constructor heads now have a `HeadType::Ctor`) | as a direct argument |
| Constructor field by name, record literal field, list item, tuple part | `may_perform_at` with the expected type, through `passed_parts` | `comp_compound` |
| An argument that is a compound of computations (`allDone [c]`) | `passed_args`: an argument is also passed if, checked against its parameter's type, it performs nothing | as a direct argument |
| A computation where a computation with an unknown row is expected (`Effect.bind c k`'s `c`) | `check_inner`: inferred with `infer_unrun` and compared, not run | |
| A value that is already a computation in the empty row (`Done 3`, `Effect.bind c k`, `identityComp c`) | `comp_check`'s last case, `returns_comp_value`: checked against the whole `Comp` type first, as the old reading's fallback | |

The last row was needed for the acceptance test `isDone (Done 3) = True`:
before, a written `Done 3` checked against `Comp NoOp NoRes ?a` was read as
the result `?a := Comp ?op ?res Nat`, leaving `?op` unsolved, and against
`Comp NoOp NoRes Nat` it was refused. It only applies in the empty row, and
only when the head's own type ends in a `Comp`.

**Not changed** (each still runs what it's given, as D1055 says; none is in
the table above, and changing them would change existing elaborations):

- Operands of `=`: `Effect.bind c Done = c` at a concrete `NoOp` row reads
  the right side as `Done (runPure c)` (the left side isn't run, since
  `bind`'s result row is unknown when it's judged). State such laws at a
  general row, as `Effect/Laws.sw` does, or with `runPure` on both sides.
- `let x := c`, unannotated: the value is run. `let x: Comp … := c` passes it.
- The branches of an `if` or `match` whose expected type is
  `Comp NoOp NoRes a`: checked against `a` and wrapped, so
  `if b then c else c` is `Done (if b then runPure c else runPure c)`.
- A parameter whose type is a type variable (`id c` with `id: a -> a`) isn't
  a computation type when the call is judged, so `c` runs.
- `Delay` (partial computations) isn't included in `is_comp_type`.
- Dot notation on a call whose result type is a named alias of a `Comp`
  (`(stuckThunk xs).finished`) finds the namespace from the unfolded type, as
  before, so it doesn't find `Thunk.finished`; on a variable it does.

**Library.** In core/Effect.sw: `Effect.foldCompDone` and
`Effect.runPureBind`. In a new file, `Effect/Laws.sw`: `Effect.bindDone`,
`Effect.bindAssoc` and `Effect.foldCompBind`, whose `Call` cases need
function extensionality (`Quot.funext`, so their one axiom is `Quot.sound`);
the core can't use `Std.Quot`. In List/Toolkit.sw: `List.mapInPure`, stated
about `Effect.runPure` and `List.mapIn` and proved as probe 3 wanted.
`Effect.translateBind` and `Effect.morphismBind` weren't attempted.

**`Fail.toResultMapIn` isn't built.** Its proof has to split on whether
`f x` fails, so it needs a lemma over a `{Fail}` computation given as a
value, proved by cases on it (`Done`, `Call (L (stop m)) k`). That lemma
can't be stated: `{Fail} b` is only allowed as a function's result type, and
the ability's result function has no source name, so no binder can have the
type of a `{Fail}` computation. A thunk `() -> {Fail} b` can be a binder, but
`match first () with …` runs the call. Function extensionality isn't the
obstacle: since `Fail` never resumes, the split needs no induction. What's
missing is a way to name the type (a `{Fail} b` binder type), which belongs to
stage 1's design.

**Tests.** `examples/accept/effect-pass-computations.sw` has, for each path, a
written `Done` seen as `Done` and a stuck call that computes to `Done`, plus
`runPure (identityComp (Done n))`, probe 1's law and probe 3's proof.
`examples/reject/effect-pass-*.sw` has one file per path where an arbitrary
computation would have been `Done`: direct, stuck (probe 4), piped, dot,
field, named field, named argument, record, list, tuple, identity.

## As built (stage 1, first part)

SW-406, 24 Oct 2026. Design C's row-indexed computation type, the internal
row boundary, and inferring rows. `List.mapIn` isn't folded into
`List.map` yet (stage 3).

**Library** (`core/Effect.sw`). `Effect.Sig`, `MkSig`, `sigOp` and
`sigRes` are gone. In their place, after `runPure`:

```
type Effect.Effects: Type 1 =
  | Empty
  | Ops (op: Type) (res: op -> Type)
```

with `rowOp`, `rowRes` (`rowOp Empty` is `NoOp`), `CompIn` (`CompIn Empty
a` is `a`, `CompIn (Ops op res) a` is `Comp op res a`), `doneIn`, `bindIn`,
`liftIn` (`Done` at `Empty`) and `lowerIn` (`runPure` at `Empty`), each by
cases on the row, as in §5.C. They are registry built-ins (`Builtin::Row`,
`RowEmpty`, `RowOps`, `RowOp`, `RowRes`, `CompIn`, `DoneIn`, `BindIn`,
`LiftIn`, `LowerIn`), which replace `Sig`, `SigOp` and `SigRes`. The
printer shows `CompIn e a` as `{e} a`. (The type was named `Row` when stage 1
was first built; D1143 (a) renamed it `Effects`. The built-in is still
`Builtin::Row`.)

**Types.** A row variable `e` has type `Effects`. `{A | e}` is a `Comp` whose
operations end in `rowOp e`, as before with `sigOp`. A bare `{e} a` is
`CompIn e a` (`effects::comp_type`); `comp_parts` reads a `CompIn` stuck on
its row as the bare row `{e}`. A row with abilities, or a closed one, is a
`Comp` as before. So at the empty row a function of type `a -> {e} b` is a
function of type `a -> b`.

**Computation mode in a bare row.** `done` writes `doneIn e v`, and
`sequence`, `wrap` and an operation's argument use `bindIn e`
(`effects::bind_term`). `lift`, moving a computation of a callee's row
into the current one:

- from a bare `{f}` whose `f` turned out `Empty`: the value is plain; it
  becomes `done` in the current row, and at the empty row `in_place` takes
  the value out of that `Done` again, so a pure call of `mapIn` is just
  `List.mapIn [Empty] …`, with no `runPure`;
- from a bare `{f}` into a row with abilities, or a partial one: `liftIn f`
  first, then `translate` (and `lift` into `Delay`) as before;
- into a bare `{e}` from a row that isn't the same bare row (a hand-written
  `Comp NoOp NoRes a`, say): `translate`, then `lowerIn e`.

A handler whose remaining row is a bare `{e}` forwards an operation as
`lowerIn e (Call (sigInject m o) (y => liftIn e (k (sigReply m o y))))`,
since its clauses' results are `CompIn e t`.

Canonical rows: `effects::row_value` writes `Empty` for the empty row, the
row variable itself for a bare `{f}`, and `Ops (ops row) (res row)` only for
a row with at least one ability. `solve_tail` and `extend_with` use it, and
the unifier's rule (below) never makes `Ops NoOp NoRes`.

**Inferring rows (D1123, D1124).** `unify::row_rule`, a case of
`unify_step`, applies when one side is `CompIn ?e B` for an unsolved,
unfrozen row unknown and the other side is neither an unknown nor another
`CompIn` (those keep the ordinary rules: `?T := CompIn ?e B`, and the
spine rule). After forcing the other side `T`:

| `T` | Result |
|---|---|
| a data type other than `Comp`, a function type, a sort, an equation, a type variable, a quotient, an opaque primitive | `?e := Empty`, then `B ≟ T` |
| `Comp op res A`, `op` headed by `Plus` | `?e := Ops op res`, then `B ≟ A` |
| `Comp NoOp NoRes A` | `?e := Empty`, then `B ≟ T` (data) |
| `Delay …` | no: a row variable never stands for `Partial`, so the partial-callback error is unchanged |
| a definition stuck on an unknown or a variable, or a `Comp` whose operations are stuck | blocked |

A blocked comparison fails, except under `unify::unify_postponing`, which
`check::compare` calls after the other fallbacks (instances, `coerce`)
fail. It records the blocked pairs (`unify::RowConstraint`, with their
level) and succeeds; `compare` keeps them (`rows::postpone`) and accepts
the term. Kept comparisons are retried in the rounds of `solve_obligations`
(`Elaborator::retry_rows`: both sides read back and evaluated again, so a
definition stuck on an unknown solved since takes its step); settling one
is progress. At the end of a declaration, `Elaborator::settle_rows` (called
from `finish`) retries them until nothing changes, then defaults: every row
unknown made for an implicit parameter of type `Row`
(`check::implicit_arg` notes them, `rows::note_row_meta`) that is still
unsolved is set to `Empty`; then the obligations and the comparisons are
retried, and a comparison still put aside is reported as a mismatch. Both
lists are part of the undo snapshot and are cleared with the metavariables.

The SW-393 coercion (`coerce`, a pure function where an effectful one is
expected) still runs, for a rigid row variable (`f: a -> b` passed where
`a -> {e} b` is expected inside a definition with its own `e`: `doneIn e`
around the call) and for rows with abilities (`Done` around it). For an
unknown bare row the unifier now settles it first.

**The boundary (D1122).** `Elaborator::resolve` doesn't find
`Effects.Empty`, `Effects.Ops`, `rowOp`, `rowRes`, `CompIn`, `doneIn`, `bindIn`,
`liftIn` or `lowerIn` outside the library (`loading_prelude`), and
`unknown` reports such a name as `E-INTERNAL`. One change from D1122 as
written: the *type* `Effect.Effects` can be named by programs. A program needs
it to declare a type with a row parameter (`type Handlers (e: Effects)` in
`examples/accept/partial.sw` and `crates/driver/tests/partial.rs`, which
named `Effect.Sig` before). Without the constructors and eliminators a
`Effects` value can only be passed on, so parametricity holds. An import of an
internal name is accepted; using it isn't.

**Tests.** `examples/accept/effect-rows.sw`: probe 5's three theorems with
`List.mapIn` in place of `mapR`, by the same proofs, and one definition and
test per row of the worked-examples table (§5.C.1): `Nat`, `List a`, a
function type, a record, a result type found later, a type that becomes a
`Comp` only once an unknown is solved (`Answer ?flag`, solved by the list
after the callback: put aside, then effectful in `Log`; the same with
`False`: pure), an effectful callback, a dependent result type (`Vec Nat
3`), a type family stuck on a variable (`Cell x` through a dependent
`applyDep`), and a row-polymorphic callback, pure and effectful.
`examples/reject/row-internal-constructor.sw` (`Effect.Effects.Empty` in
`[e := …]`), `row-internal-inspect.sw` (`Effect.rowOp`) and
`row-internal-match.sw` (matching on `Empty`/`Ops`) are `E-INTERNAL`; the
old `row-tail-repeats-ability.sw` (a hand-built `Sig` repeating an ability)
is now that first file, since a program can't build a row at all.
`crates/driver/tests/empty_row_kernel.rs` gained
`a_pure_use_of_an_effect_polymorphic_function_has_no_computation` (no
`Comp`, `Done`, `runPure` or `Ops` in the term, an `Empty` row present, and
`{}` is no row), and the handler-equation test now expects no `runPure`.
In std, `List.mapInPure` is now `List.mapIn f xs = List.map f xs` with
`map`'s proof, and `List.lengthMapIn` is `List.lengthMap`'s proof.

**D1133 and D1134: options, not built.** Both turned out to need a
language-design choice, so they are written up here and stop for a
decision.

*D1133: equation operands and branches whose type is a computation.* Under
C the question only concerns `Comp` types written by hand at the empty row
(`Comp NoOp NoRes a`) and computations over abilities given as values (a
`{Fail} b` binder, D1134). A bare row is settled by unification: `List.mapIn
f xs = List.map f xs` already compares `CompIn ?e (List b)` with `List b`
and picks `Empty`. But D1134 makes the question real: with a binder
`c: {Fail} b`, `c = Done x` or `Fail.toResult (() => c) = …` must not run
`c` in place (in a pure context that is `E-ABILITY`).

- (a) **[Recommended]** A part whose own type is a computation type is
  passed where it's written: an operand of `=` (the other side is checked
  against its type), and each branch of an `if` or `match` checked against a
  `Comp` type that was written as one (the expected type of a check, not
  the computation mode of an enclosing effectful body). This extends stage
  0's rule from places to values. It changes the reading of an equation
  between `Comp NoOp NoRes` computations stated at that concrete row (std
  has none: `Effect/Laws.sw` states its laws at a general row), and of an
  `if` checked against such a type (`if b then c else d` is no longer `Done
  (if b then runPure c else runPure d)`). Over a row with abilities it only
  accepts what's refused today.
- (b) Keep stage 0's behaviour: state such laws at a general row or with
  `runPure` on both sides, and state SW-378's lemma about thunks (`() ->
  {Fail} b`) with handlers applied to them, never about a computation as a
  value. Nothing changes, but `Fail.toResultMapIn`'s case split (§ "As built
  (stage 0)") stays unstatable.
- (c) Only `=`, not branches.

*D1134: writing a computation type as a binder's type.* `{Fail} b` is
parsed only after `->`; elsewhere `{` starts a record literal or update, so
`(c: {Fail} b)` is a parse error ("expected `|` and the fields to update").

- (a) **[Recommended]** `{A, B | e} T` is a type wherever a type is written:
  binder and `let` annotations, type arguments, constructor fields, and a
  definition's result. The parser tells it from a record by its contents: a
  row lists abilities (names applied to arguments, a `| e` tail) and has no
  `=` before its closing `}`, and is followed by a type. `effect_type`
  already elaborates `Expr::Effect` wherever a type is checked, so the
  elaborator needs nothing new; `{e} b` as a binder's type is `CompIn e b`,
  whose constructors stay internal, so a program can pass such a value or
  sequence it but not match on it unless the row is concrete.
- (b) Only in binder annotations (`(c: {Fail} b)`, `[c: …]`, `let c: … :=`),
  where nothing else can start with `{`.
- (c) No new syntax; SW-378's lemma is stated about a thunk and proved with a
  helper whose parameter is written as `Comp` with the ability's types read
  off a function (as `opsOf`/`resOf` did in the old reject example).

(a) of D1134 needs (a) or (c) of D1133 to be useful for SW-378.

**Remaining for stage 1** (a follow-on lane):

1. D1133 and D1134, once decided (parser and `may_perform` changes), then
   `Fail.toResultMapIn` (SW-378).
2. Share the apartness classification with the instance search's
   `rigidly_distinct` (`interfaces.rs`), as §5.C.1 asked; `row_rule` has its
   own copy.
3. A callback checked by eta-expansion (a lambda, or a variable of function
   type checked against `a -> {e} b`) has its body checked in the row
   `{?e}`'s computation mode, where a pure body of type `T` is compared with
   `B`, not `CompIn ?e B`, so `row_rule` doesn't see it. Where no row fits
   (`examples/reject/row-stuck-callback.sw`) that gives the right error;
   whether it ever refuses a program that has a row hasn't been looked into.
4. Speed is unchanged (design E, stage 2): unspecialised code passes
   `{ tag: "Empty" }` and dispatches in `doneIn`/`bindIn`, as probe 6's
   `mapR` did.

Done since (same lane): the note on an error after defaulting. `default_rows`
returns where each defaulted row unknown was made, and an error found after
defaulting (by the obligations or the comparisons retried, or a comparison
still put aside) gets a label on that call, "the row of this call was set to
the empty row", and a note saying why
(`examples/reject/row-defaulted.sw`). Unit tests of `row_rule`, one per row
of its table, against `unify` and `unify_postponing` (`rows.rs`, `tests`).

## As built (stage 1, remainder)

SW-406, 24 Oct 2026.

**D1140 (a).** Two of stage 0's "Not changed" places now pass a computation
as written:

- *Operands of `=`.* An operand whose own type, read off its head's type, is
  a `Comp` (any row: `Comp NoOp NoRes a`, or an effectful call such as
  `thunk ()` with `thunk: () -> {Abort} Nat`) is passed
  (`effects::passed_operand`): `may_perform` doesn't count it,
  `comp_compound` doesn't run it first, and the group infers it with
  `infer_unrun` (`numbers::speculate`); the other side is checked against
  its type. So `Effect.bind c Done = c` at `NoOp` is what it says
  (`Effect.bindDone c` proves it), and `f = 3` with `f: Comp NoOp NoRes Nat`
  is `f = Done 3`. A computation in a bare row (`CompIn e a`, what
  `List.mapIn` returns) isn't passed this way: its row is inferred from the
  other side, as before. `!=` and `==` are unchanged.
- *Branches.* A check against a computation type (`check_inner`) uses
  `effects::comp_check_written`: in the empty row an `if`'s or a `match`'s
  branches (also after a `let`) are checked against the whole
  `Comp NoOp NoRes a`, so `if b then c else d` is that, not
  `Done (if b then runPure c else runPure d)`. Computation mode (`run_pure`,
  handler clauses) still checks them against `a` and wraps the result.

Tests: `examples/accept/effect-pass-equations.sw`,
`examples/reject/effect-pass-branch.sw` and `effect-pass-equation.sw` (each
checked before the change, so they test the new path).
`empty_row_kernel.rs`: `c () = c ()` over `{Abort}` is now accepted
(`an_equation_between_computations_compares_them`); the refusal test uses
`c () + 1`, which still runs `c ()`. `accept/empty-row-run.sw`'s
`fIsThree` now states `f = Done 3` (its hash moved; nothing else's did).

**One apartness classification.** `unify::rigid_head` says what a value is
at its outermost layer when no solution of an unknown can change it (a data
type, a function type, a sort, an equation, a variable applied or not, a
quotient type, a definition that never unfolds). `row_rule` decides `Empty`
when the other side has one (after `Comp` and `Delay`), and the instance
search's `rigidly_distinct` calls two values distinct when their rigid heads
differ. Where the two copies had differed, the shared one takes the stricter
reading on each point:

- a stuck `Quot.lift` (a type-valued one stuck on an unknown may yet compute
  to a `Comp`) is now blocked in `row_rule`, not apart; `Quot.mk`,
  `Quot.ind` and `Quot.sound` aren't types, so the rule says nothing;
- `rigidly_distinct` now also sees an applied variable, a quotient type and
  a definition that never unfolds (`Delay`) as rigid, where before it fell
  back to asking whether an unknown was left (blocked if so).

No test, std or AoC hash moved. `rows.rs` has a unit test for the quotient
cases.

**Eta-expanded callbacks.** Item 3 of the remaining list did refuse
programs that have a row: `List.mapIn (tagged => answer tagged) numbers`
in a `{Log}` body was `E-TYPE-MISMATCH` ("expected `List Nat`, but this has
type `List ({Log} Nat)`") while `List.mapIn answer numbers` was accepted,
since the body `answer tagged: Answer ?flag` was checked against `?b`
(solving `?b := Answer ?flag`) and the row defaulted to `Empty` before
`?flag` was known. Now `effects::unknown_row_value` infers a call-like body
(a variable, a call, a dot call or a pipe that performs nothing) in a bare
row whose row is still unknown and compares its type with the whole
`CompIn ?e b`, so `row_rule` decides: `Empty` (the value is `doneIn ?e v`,
the same term as before), the computation's row, or put aside. If that
fails, the body is checked against `b` as before. Regression tests:
`loggedLambda` and `notLoggedLambda` in `examples/accept/effect-rows.sw`; no
existing hash moved. Still refused, and not an eta case: a `let` that binds
`List.mapIn answer numbers` in a `{Log}` body and returns it later (the row
is defaulted before the `let`'s variable is compared with the result type).

## Appendix A. Probe files

All are in a scratch directory, checked with `stitchwort check FILE`.

**Probe 1** (fails at `c`):

```
import Std (Effect)

theorem runPureBindA [a b: Type]: (c: Effect.Comp Effect.NoOp Effect.NoRes a) -> (k: a -> Effect.Comp Effect.NoOp Effect.NoRes b) ->
    Effect.runPure (Effect.bind c k) = Effect.runPure (k (Effect.runPure c))
  | Done x, k => rfl
  | Call () rest, k
```

**Probe 2** (checks):

```
import Std (Effect, List)
import Std.Effect.Comp (Done, Call)

def runPureNo [a: Type] (c: Effect.Comp Effect.NoOp Effect.NoRes a): a := Effect.runPure c

def bindNo [a b: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> (a -> Effect.Comp Effect.NoOp Effect.NoRes b) -> Effect.Comp Effect.NoOp Effect.NoRes b
  | Done x, k => k x
  | Call () rest, k

theorem runPureBindNo [a b: Type]: (c: Effect.Comp Effect.NoOp Effect.NoRes a) -> (k: a -> Effect.Comp Effect.NoOp Effect.NoRes b) ->
    runPureNo (bindNo c k) = runPureNo (k (runPureNo c))
  | Done x, k => rfl
  | Call () rest, k
```

**Probe 3** (everything checks except the last clause):

```
import Std (Effect, List, Eq)
import Std.Effect.Comp (Done, Call)

def runPureNo [a: Type] (c: Effect.Comp Effect.NoOp Effect.NoRes a): a := Effect.runPure c

def bindAt [a b: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> (a -> Effect.Comp Effect.NoOp Effect.NoRes b) -> Effect.Comp Effect.NoOp Effect.NoRes b := Effect.bind

theorem runPureBindAt [a b: Type]: (c: Effect.Comp Effect.NoOp Effect.NoRes a) -> (k: a -> Effect.Comp Effect.NoOp Effect.NoRes b) ->
    runPureNo (bindAt c k) = runPureNo (k (runPureNo c))
  | Done x, k => rfl
  | Call () rest, k

def mapInPure [a b: Type] (f: a -> b) (xs: List a): Effect.Comp Effect.NoOp Effect.NoRes (List b) := List.mapIn f xs

theorem mapInIsMap [a b: Type] (f: a -> b): (xs: List a) -> runPureNo (mapInPure f xs) = List.map f xs
  | Nil => rfl
  | Cons x xs => Eq.trans (runPureBindAt (mapInPure f xs) (rest => Cons (f x) rest)) (Eq.cong (Cons (f x)) (mapInIsMap f xs))
-- E-TYPE-MISMATCH: expected `Effect.runPure (Effect.bind (List.mapIn (_ => Done (f _)) xs) (%8 => Done (Cons (f x) %8))) = …`,
--                  but this has type `Cons (f x) (Effect.runPure (List.mapIn (_ => Done (f _)) xs)) = …`
```

**Probe 4** (checks, which shows the argument was run in place):

```
import Std (Effect, List, Eq)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done x => True
  | Call () rest

def stuckComp [a: Type]: List a -> Effect.Comp Effect.NoOp Effect.NoRes Nat
  | Nil => 0
  | Cons x xs => 1

theorem argumentIsRunInPlace: (xs: List Nat) -> isDone (stuckComp xs) = True := xs => rfl
```

**Probe 5** (checks):

```
import Std (Effect, List, Eq)
import Std.Effect.Comp (Done, Call)

type Row: Type 1 =
  | Empty
  | Ops (op: Type) (res: op -> Type)

def CompR: Row -> Type -> Type
  | Empty, a => a
  | Ops op res, a => Effect.Comp op res a

def doneR [a: Type]: (row: Row) -> a -> CompR row a
  | Empty, x => x
  | Ops op res, x => Done x

def bindR [a b: Type]: (row: Row) -> CompR row a -> (a -> CompR row b) -> CompR row b
  | Empty, c, k => k c
  | Ops op res, c, k => bindOps c k

def bindOps [op: Type] [res: op -> Type] [a b: Type]: Effect.Comp op res a -> (a -> Effect.Comp op res b) -> Effect.Comp op res b
  | Done x, k => k x
  | Call o rest, k => Call o (y => bindOps (rest y) k)

def mapR [a b: Type] (row: Row) (f: a -> CompR row b): List a -> CompR row (List b)
  | Nil => doneR row Nil
  | Cons x xs => bindR row (f x) (y => bindR row (mapR row f xs) (ys => doneR row (Cons y ys)))

-- then mapREmpty, lengthMapR and mapRCons as in §4
```

**Probe 7, the suspending effect** (`stitchwort test` passes; built with
`stitchwort build --js` and run natively with a `main` that sums the
result of `List.range size`):

```
import Std (List)

ability Counter where
  next: () -> {Counter} Nat

def Counter.number (prog: () -> {Counter} a): Nat -> a :=
  handle prog() with
    | return x => (s => x)
    | Counter.next u, k => (s => k s (s + 1))

export def labelAll (numbers: List Nat): List Nat :=
  Counter.number (() => List.mapIn (x => x + Counter.next()) numbers) 0

test "labels" := labelAll [10, 10, 10] == [10, 11, 12]
```

The JS benchmark imports the generated module, with the internal
`List.map`, `List.mapIn`, `Effect.runPure` and `double` re-exported, and
times each variant on a prebuilt internal list after one warm-up run (20
repetitions up to 10,000 elements, 3 above).

**Probe 8** (each theorem checks, which shows the argument was run in
place; the last definition is refused):

```
import Std (Effect)
import Std.Effect.Comp (Done, Call)

def isDone [a: Type]: Effect.Comp Effect.NoOp Effect.NoRes a -> Bool
  | Done x => True
  | Call () rest

def identityComp (c: Effect.Comp Effect.NoOp Effect.NoRes Nat): Effect.Comp Effect.NoOp Effect.NoRes Nat := c

theorem variableIsRunInPlace: (c: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> isDone c = True := c => rfl

theorem throughIdentity: (c: Effect.Comp Effect.NoOp Effect.NoRes Nat) -> isDone (identityComp c) = True := c => rfl

export def useIt (n: Nat): Nat := Effect.runPure (identityComp (Done n))
-- E-TYPE-MISMATCH at `Done n`: expected `Nat`, but this has type `Comp (?0 n) (?1 n) Nat`
```

(The two theorems and `useIt` were run as separate files.)

**Probe 9** (each file checks):

```
import Std (Effect, List)

def explicitRow (xs: List Nat): List Nat :=
  List.mapIn [e := Effect.Sig.MkSig Effect.NoOp Effect.NoRes] (x => x + 1) xs

def leak (f: Nat -> {e} Nat): Effect.Sig := e
```

```
import Std (Effect, List)
import Std.Effect.Sig (MkSig)

def inspect: Effect.Sig -> Bool
  | MkSig op res => True

def pickRow [e: Effect.Sig] (f: Nat -> {e} Nat): Bool := inspect e
```

and `def keepRow (f: Nat -> {e} Nat): List Effect.Sig := [e, e]` is refused
with `E-UNIVERSE` ("expected something of type `Type`, but this has type
`Type 1`").

**Probe 10** (refused with `E-UNIVERSE`):

```
ability Gen where
  gen: Type -> {Gen} Nat
```

**Probe 11** (refused with `E-UNSOLVED` at the `List.mapIn` call):

```
import Std (List)

def unconstrained: Nat :=
  let unused := List.mapIn (x => x + 1)
  0
```

**Theorem count** (§2.2): a Python script reads every `.sw` file under
`crates/elab/src/std/`, takes each `theorem` line plus its indented
continuation lines up to `:=` or a line starting with `|`, and counts the
statements that contain the full name (`List.map`, not preceded by a letter,
digit or dot, and not followed by a letter or digit).

## Appendix B. Small issues found on the way

- The note on `E-UNKNOWN-NAME` for `Done` suggests
  `import Effect.Comp (Done)`, which fails with `E-IMPORT-UNKNOWN`; the
  working form is `import Std.Effect.Comp (Done)` **[checked]**.
- `Effect.bind [Effect.NoOp] …` reads `[Effect.NoOp]` as a list
  **[checked]**. Named implicit arguments do work: probe 1's statement
  written with `Effect.bind [op := Effect.NoOp] [res := Effect.NoRes] c k`
  checks (revision, at `2934c86e`) **[checked]**. The first version said
  there was no such syntax; that was wrong by the time of the revision.
- The `E-UNKNOWN-NAME` note for `Effect.MkSig` suggests adding
  `import Std (Effect)` even when that import is present (seen in probe 9's
  first attempt) **[checked]**. This looks like the import-hint bug already
  filed on the board **[inferred]**.

# Effect polymorphism: one function for pure and effectful callbacks

Status: design note and literature review, not decided (D1110; decisions
D1116 to D1121 in §7). Nothing is built. The two experiments before this
note are in [effectful-map.md](effectful-map.md).

Claims about the codebase cite `file:line` and are marked **[checked]** (read
in the source on `main` at `754128ca`, or run with
`target/release/stitchwort` built from `main` on 24 Oct 2026 and Node
22.23.3) or **[inferred]**. Claims about other languages and papers cite a
URL. **[unverified]** marks claims written from memory without a source I
could open. The probe files are in Appendix A, so a reader can rerun them.

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
   2008). The known fix is to represent computations in continuation-passing
   style at runtime, which Koka and Effekt do.
4. **One source-language fix is needed by every design.** Today a
   computation passed as an argument at the empty row is always run in place
   and re-wrapped as `Done (runPure c)`, even when the parameter's type is a
   `Comp` (probe 4). So no lemma about a stuck computation can ever be
   used. Passing the computation unchanged when a computation is expected
   fixes this, and makes `runPure (mapIn f xs) = map f xs` provable.

**Recommendation** (D1116 to D1121): adopt the row-indexed computation type
(design C), preceded by the argument-passing fix (stage 0) and followed by
empty-row specialisation in both backends (design E). Fold `mapIn` into
`map` only after both, and extend the convention to other functions one at
a time as programs need them. Fix the quadratic effectful case with a
continuation-passing runtime representation (design F) as its own stage.

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
**[unverified]**. *For Stitchwort:* "zero cost when unused" is achieved by
compile-time specialisation, not by a cleverer runtime. The same holds for
design E.

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
computation.

### 3.3 What the survey says, in short

- No prover unifies pure and monadic `map` definitionally today. Lean, the
  closest, uses two names, a bridging lemma and a compiler attribute.
- Compilers that make effect polymorphism free when no effect is performed
  all do it statically: Koka's selective translation and fast paths, Effekt's
  staging, Eff's type-directed rewrites. The runtime representation of
  computations differs from the semantic one in all of them.
- Free-monad encodings need a CPS or queue representation at runtime to
  avoid quadratic binds.

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

### B. A kernel rule: `runPure (bind c k)` reduces at `NoOp`

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
- Unification: `CompIn ?e B` against a plain type `T` can't be inverted in
  general. The elaborator needs a rule: if `T`'s head is not `Comp`, solve
  `?e := Empty` and `B := T` (the only solution, since `CompIn (Ops …) B`
  is a `Comp`); if `T` is a `Comp`, postpone. This replaces the SW-393
  coercion for the bare-row case. An unsolved `?e` at the end of a pure
  definition defaults to `Empty`.
- Two spellings of "empty": `Empty` and `Ops NoOp NoRes` would both be
  values of `Row`. The elaborator must always produce `Empty` for an empty
  row; `Ops NoOp NoRes` would still work, as a tree.
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
  Matt wants to avoid, hidden from users.

### E. Backend specialisation at the empty row

For each row-polymorphic definition used at the empty row, the backend
makes a copy with the row fixed and simplifies it:

- Under design C, the row argument is the constructor `Empty`. Fixing it,
  inlining `bindIn Empty c k` to `k c` and `doneIn Empty v` to `v`, and beta
  reducing turns `map`'s body into `Cons (f x) (map_Empty f xs)`, which the
  existing TRMC pass makes a loop **[inferred]**; the result is
  `List.map`'s code (probe 7, "specialised").
- Under today's encoding, the backend would have to see that the row
  argument is `MkSig NoOp NoRes`, normalise each `bind`'s implicit `op`
  argument to `NoOp`, and apply type-directed rewrites (`Done v → v`,
  `bind c k → k c`, `runPure → id`). Possible, since the JS backend works
  from kernel terms before erasure, but it needs the kernel evaluator in
  the backend and changes the runtime representation of values of type
  `Comp NoOp NoRes a`, which must then never meet unspecialised code
  **[inferred]**.
- Copies are made transitively from each use: a specialised function's
  calls with rows derived from its own `Empty` are specialised too. A copy
  is keyed by (definition hash, row constructor), so it is made once per
  program.
- The native runtime (`crates/rt`) gets the same pass in its lowering; it
  shares erasure decisions with JS (`crates/rt/src/lib.rs:11`) **[checked]**.
- Hashing: copies are backend artefacts, not hashed definitions.
- Stack: specialisation removes the overflow for pure uses, because the
  copy is a loop. It does nothing for genuinely effectful uses (design F).

### F. A different runtime representation for effectful code

Keep `Comp` as the kernel's semantics; change only how the backends run
it:

1. **Bind-inlining fast path** (Koka, §3.1): compile `bind c k` as
   `case c of Done x -> k-body | Call … -> slow path`, with join points so
   code size stays linear. Recursion stays tail recursion on the `Done`
   path, so TRMC applies within one function.
2. **CPS (codensity) representation** for the slow path: a computation is
   a function taking "what to do with the result" and "what to do with an
   operation". `bind` becomes O(1) and the quadratic behaviour of probe 7
   goes away (Voigtländer 2008). A trampoline (a loop that runs one step
   at a time) keeps JS's stack bounded, as Links' JS backend does
   (FSCD 2017). This is the fix for SW-396 and for the quadratic case.
3. **Tail-resumptive handlers in place** (Koka, §3.1): a handler clause of
   the form `op x k => k e` (or, for a state-passing handler, `s => k v s'`)
   runs at the call site without building a continuation.

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

### Comparison

| | A | B | C | D | E | F |
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
B is less elaborator work but puts a non-standard rule in the kernel with a
confluence caveat, and covers only `bind` directly under `runPure`.

| Stage | Work | Lanes, rough cost | Acceptance |
|---|---|---|---|
| 0 | Elaborator: pass a computation where a `Comp` is expected. Library: `Effect.runPureBind`, `Effect.foldCompBind`, `List.mapInPure`, `Fail.toResultMapIn` | 1 lane, small | Probe 4's theorem is refused (the argument is now passed); probe 3 checks; the four theorems check; targeted effect tests and `examples/accept/effect*` pass |
| 1 | Design C: `Row`, `CompIn`, `doneIn`, `bindIn`, `liftIn`, `lowerIn` in `core/Effect.sw`; elaborator uses them for bare row variables; unification rule `CompIn ?e B ≟ T`; default `?e := Empty` | design review, then 1 to 2 lanes, large | probe 5's three theorems hold with `List.mapIn` in place of `mapR`, by the same proofs; every existing effect example and AoC day using `mapIn` checks unchanged in source |
| 2 | Design E in JS and rt: specialise on a known `Row` constructor, inline non-recursive dispatchers, then TRMC | 1 lane per backend, medium | the JS for `List.mapIn` used at `Empty` is the same loop as `List.map` (diff of the two functions modulo names); within 10% of `map` at 1,000,000 elements; 1,000,000 elements on both backends with a pure callback |
| 3 | Fold: `map` gets `mapIn`'s signature, `mapIn` is deleted, callers renamed | 1 lane, small | all 78 statements and their proofs check with no source change; std, AoC and examples pass; JS benchmark of `map` within 10% of today |
| 4 | Design F: bind-inlining fast path and CPS-plus-trampoline slow path in JS; CPS representation in rt | design note, then 1 to 2 lanes, large | `labelAll` (probe 7) on 1,000,000 elements runs on both backends; doubling `n` at most 2.5 times the time; differential tests against the reference evaluator pass |
| 5 | Further functions as needed (`foldLeft`, `filter`, `any`/`all`/`find`, `Option.map`, a new `forEach`) | 1 small lane each | each function's existing lemmas check unchanged |

Stages 0 and 2 are independently useful: stage 0 makes effectful lemmas
possible at all, and stage 2 speeds up today's pure uses of `mapIn` and of
handlers with open rows.

## 7. Decisions for Matt

**D1116. Direction for effect-polymorphic library functions.**
(a) Status quo: separate pure and effectful functions with a proved bridge
each (design A, as Lean does).
(b) A kernel reduction rule for `runPure (bind c k)` at the empty signature
(design B).
(c) **[Recommended]** A row type with a separate empty row, and a
computation type defined by cases on it, so the empty row is the plain type
(design C).
(d) Proven replacements for the backends only (design D).
Reason: (c) is the only option where the existing proofs check unchanged
with no new kernel rule (probe 5).

**D1117. Pass computations where a computation is expected (stage 0).**
(a) **[Recommended]** Yes, now, whatever D1116 decides.
(b) No: keep running every computation argument at the empty row.
Reason: without it no lemma about a stuck computation can be used (probe 4),
in any design.

**D1118. Making pure uses fast in the backends.**
(a) **[Recommended]** Specialise row-polymorphic definitions at the empty row
in JS and rt (design E).
(b) Dynamic dispatch only: no specialisation, accept slower pure uses.
(c) A `csimp`-style attribute with a proven twin per function (design D).
Reason: (a) restores today's loop with no twins, and under (c) of D1116 it
is generic constant folding.

**D1119. The quadratic, stack-hungry effectful case (SW-396 and probe 7).**
(a) **[Recommended]** A later stage (stage 4): CPS representation with a
trampoline for effectful code in both backends, with a Koka-style
bind-inlining fast path.
(b) Only a trampoline for JS stack safety; leave the quadratic time.
(c) Defer until a program is hurt by it.
Reason: an effectful `map` over 4,000 elements already fails in JS and
32,000 take a minute natively, so Unison-style library functions aren't
usable for real inputs without it.

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

**Theorem count** (§2.2): a Python script reads every `.sw` file under
`crates/elab/src/std/`, takes each `theorem` line plus its indented
continuation lines up to `:=` or a line starting with `|`, and counts the
statements that contain the full name (`List.map`, not preceded by a letter,
digit or dot, and not followed by a letter or digit).

## Appendix B. Small issues found on the way

- The note on `E-UNKNOWN-NAME` for `Done` suggests
  `import Effect.Comp (Done)`, which fails with `E-IMPORT-UNKNOWN`; the
  working form is `import Std.Effect.Comp (Done)` **[checked]**.
- There is no syntax for giving an implicit argument explicitly:
  `Effect.bind [Effect.NoOp] …` reads `[Effect.NoOp]` as a list
  **[checked]**. Whether named arguments (D1092) will allow
  `Effect.bind (op := Effect.NoOp)` is **[unverified]**.

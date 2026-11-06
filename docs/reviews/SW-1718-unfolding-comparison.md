# How other systems keep the elaborator from unfolding too far

A comparative study for SW-1718, written 6 November 2026 against
[bounded-readback.md](../proposals/bounded-readback.md) (SW-1712, D2514, draft 1), with
[goal-as-written.md](../proposals/goal-as-written.md) and
[goal-readback.md](../proposals/goal-readback.md). Both of those already have a prior-art
section on `rewrite` and `match` (goal-as-written.md §3, goal-readback.md §3). This study
doesn't repeat them. It covers the other concerns: unification and zonking, printing,
`decide`, resource limits, and opacity.

Labels:

- **[checked]**: read in the system's source or manual at the place cited, on 6 Nov 2026.
- **[recalled]**: from my knowledge of the system, not re-read for this study. Treat these
  as likely but not certain.
- **[inferred]**: my reasoning from the above.

Nothing was built or run: this lane was read-only, plus the web.

## Contents

0. [Summary](#0-summary)
1. [The table](#1-the-table)
2. [Each system](#2-each-system)
3. [Lessons for bounded-readback.md](#3-lessons-for-bounded-readbackmd)
4. [Suggested changes to the note](#4-suggested-changes-to-the-note)
5. [What this study did not do](#5-what-this-study-did-not-do)
6. [Sources](#6-sources)

## 0. Summary

**The problem everyone has is the one Stitchwort has.** Lean and Agda both have Stitchwort's
"rule 2". Lean's `whnf` turns a `match` on an unknown structure into a match on its
projections (`toCtorWhenStructure` [L3]). Agda compiles a record pattern into projections
(`RecordPatterns.hs`: "replaces pattern matching on record constructors with uses of
projection functions" [A5]). Neither blows up in everyday use, because neither elaborator
normalises the goal in full at the places listed in bounded-readback.md §2. Agda's `with`
and `rewrite` are the exception: they do normalise the goal in full, and Agda's manual warns
about exactly this cost [A1]. **[checked]**

**How the others bound unfolding.** Lean, Rocq and Agda don't put a cap on size. They control
*which definitions* may unfold, and they work lazily (weak head normal form, keyed matching,
lazy conversion), so a large unfolding is never built. Every one of them has per-declaration
opacity settings, and Lean and Idris 2 also set some by default without annotation:

- Lean marks functions defined by well-founded recursion `@[irreducible]` [L13].
- Idris 2 doesn't reduce a definition outside its namespace unless it is `public export` [I3].

Fixed caps that *change the answer* are rare. Idris 2 is the clear case:

- Meta solutions are read back with only inline definitions unfolded, and a size limit of 25
  stuck applications (`%nf_metavar_threshold`). Past it, the read-back falls back to the
  unfolded form [I2, I4].
- Its evaluator has a `fuel` that keeps a call as it is when it runs out [I1].

Caps on *printing* are common: Lean's `pp.maxSteps` is 5,000 nodes [L6], and Rocq's
`Printing Depth` is 50 [R5]. Caps on *work* are common too, and when hit they are errors,
not different answers:

- Lean has `maxHeartbeats`, a count of allocations labelled "(deterministic) timeout" [L7],
  and `simp`'s `maxSteps`, which defaults to 100,000 [L8].
- Rocq has `Timeout` in seconds and `AllocLimit` [R5].

**What this means for the note.** The note's core choice is confirmed: look as written, open
a call only when the answer could be inside, and read output terms folded. smalltt and
Idris 2 do the same for meta solutions [K1, I2]. Lean and Rocq do it for searches. What
nobody else has is a size cap that is a function of the call alone and is still
deterministic. The nearest relatives are Idris 2's fuel and its threshold, and both depend on
position or order. So D2519's main property, that a needle and its copy read alike, goes
beyond prior art rather than against it.

Two things others do that the note could take:

- **Printing elides rather than drops.** A large side becomes `⋯`; the note is not left out.
- **Exhausting a limit is not something to recover from.** Lean's ordinary `try` doesn't
  catch heartbeat or recursion-depth errors [L9].

Further suggestions are in §4.

## 1. The table

What each system does, by concern. "As written" means the term as elaborated, with solved
unknowns filled in, before any definition is unfolded.

| System | Occurrence search (`rewrite`, `match`, abstraction) | Unification and zonk | Printing goals and errors | `decide` | Resource limits |
|---|---|---|---|---|---|
| **Lean 4** | As written, keyed by head and argument count; candidates compared by `isDefEq` at `reducible` transparency; already-checked subterms cached [L1, L2] | Lazy delta: unfold one side at a time, by reducibility status and definitional height; same head, try arguments first [L4, L5]. `instantiateMVars` fills in unknowns, with no unfolding [L10] | As written. `pp.maxSteps` (5,000) and `pp.deepTerms` (depth 50) elide with `⋯` [L6] | Instance found on the proposition as written; `whnf` of `Decidable.decide p` at `default` transparency; `+kernel` has the kernel reduce it; `+native` compiles it [L11] | `maxHeartbeats` (200,000 thousand allocations, per command, deterministic), `maxRecDepth` (1,000), `simp` `maxSteps` (100,000). All are errors, and ordinary `try` doesn't catch them [L7, L8, L9] |
| **Rocq** | As written. `rewrite` takes the first match in depth-first order; with `Keyed Unification`, keyed by head, arguments up to full reduction; ssreflect: heads syntactically equal, arguments up to conversion [R1, R3] | Lazy conversion, ordered by `Strategy` levels; `Opaque` only means "unfold last" in conversion [R2]. Evar normalisation fills in, no unfolding [recalled] | As written; `Printing Depth` (50) elides with dots [R5] | No built-in `decide` on arbitrary propositions; by reflection, `vm_compute` or `native_compute` and `eq_refl`, checked by the kernel's VM. These ignore `Opaque` [R2] | `Timeout n` (wall clock, not deterministic), `AllocLimit` (allocations) [R5] |
| **Agda** | `with` and `rewrite` **normalise** the goal and argument types, then abstract syntactically. The manual warns about the cost [A1, A2] | Syntactic equality shortcut first (fuel can be set with `--syntactic-equality=N`), then reduce [A4]. `instantiateFull` fills in metas, no unfolding [A6] | "Simplified" by default: only functions that match a constructor or copattern are reduced. `C-u` gives as written, `C-u C-u` the normal form [A3] | No tactic. In the standard library, `from-yes`-style lemmas leave the conversion checker to reduce `does d` to `true` [recalled] | Depth limits for instance search (500), inversion (50) and termination (`--termination-depth`); no time or allocation limit [A4] |
| **Idris 2** | `rewrite` normalises the expected type and replaces every subterm that converts, with no key [goal-as-written.md I1] | Meta solutions read back with only inline definitions unfolded and a limit of 25 stuck applications, falling back to the full read-back [I2, I4]. Glued values hold both forms, each computed lazily [I5] | As written where it has the term (glued) [recalled] | No tactic; `decEq` and `Refl` by hand, or auto search with depth 50 [I4] | `fuel` (recursion depth: the call is kept), per-name `reduceLimit` (the call is kept), `%search_timeout` 1,000 ms (wall clock) [I1, I4] |
| **smalltt** | Not applicable (no tactics) | Glued values. Conversion starts "rigid", tries the spines of same-headed calls in "flex" mode, and unfolds on failure. Meta solutions are never unfolded and are checked up to full unfolding [K1] | Small terms "useful in error message reporting and interaction" [K1] | None | None; "bounded approximation" limits speculation [K1] |
| **cooltt (Gratzer et al.)** | Not applicable | Definitions don't unfold unless the user unfolds them locally; this is built into the type theory [G1] | As written, by construction [inferred] | None | None [inferred] |
| **Stitchwort (proposed)** | As written first, then `find` on the capped normal form (§4.2, §4.3) | `unfold_where` for zonk; `mentions` exact (§4.3) | `small(value, 10,000)`; a note is left out if its side is too large (§4.3) | Unfolded and unglued if `small(prop, 100,000)`, else as written (D2522) | `CAP` 100,000 per call (keeps the call); 10,000,000 per read-back (error) |

## 2. Each system

### 2.1 Lean 4

**Transparency instead of size.** Lean has six levels, in order `none < reducible < instances
< implicit < default < all` [L3]. Each definition has a reducibility status, and a level
unfolds the definitions whose status is at or below it [L12]. The docstring gives the reason
in performance terms:

> "During **proof automation** (`simp`, `rw`, type class resolution), we perform many
> speculative `isDefEq` calls — most of which *fail*. In this setting, we do *not* want to
> try hard: unfolding too many definitions is a performance footgun. This is why
> `.reducible` exists." [L3] **[checked]**

`semireducible` is the default status and `irreducible` is "effectively hidden from `isDefEq`
in normal usage" [L12]. Some defaults need no annotation:

- The `instance` command adds `[instance_reducible]` [L12].
- Definitions by well-founded recursion are set to irreducible "unless the user has requested
  a different setting" (`addPreDefAttributes` [L13]). **[checked the function; recalled that
  well-founded recursion and `partial_fixpoint` are its callers]**

**`whnf`, not full normalisation.** "The normalisation workhorse of Lean is `whnf`", and the
fully normalising `reduce` "is in fact rarely used" (metaprogramming book [L14]).
`instantiateMVars` "brings our expressions up to date with the current metavariable state"
and "should be used liberally" [L14]: it fills in unknowns and unfolds nothing. This is the
Lean counterpart of Stitchwort's zonk. **[checked]**

**Structure eta, smart unfolding.**

- `toCtorWhenStructure`: "If `major` is not a constructor application, and its type is a
  non-recursive structure `C ...`, then return `C.mk major.1 ... major.n`" [L3]. This is
  record eta's rule 2, under `Meta.Config.etaStruct`.
- Smart unfolding keeps a call folded unless its `match` reduces. The auxiliary `f._sunfold`
  marks each `match`, which "must be reduced, otherwise the resulting term is not
  definitionally equal"; if a marked `match` is stuck, `smartUnfoldingReduce?` fails and the
  call is not unfolded [L3]. So `f x` with `x` stuck stays `f x`. Stitchwort's
  `matches_at_once` is the same idea.

Lean gets away with rule 2 because nothing walks the whole unfolding. **[checked; the last
sentence inferred]**

**Unification.** `isDefEqDelta` is "isDefEq by lazy delta reduction" [L4]:

- If only one side can be unfolded, unfold it.
- If both sides have the same head, "First try to solve unification by unifying arguments"
  (`unfoldBothDefEq`); only if that fails, unfold both.
- Otherwise unfold by reducibility, then by the kernel's heuristic.

The kernel's `ReducibilityHints` (`opaque`, `abbrev`, `regular h`) order unfolding by
*definitional height*, "one plus the maximum height of all `.regular` constants appearing in
the definition's body". They "only affect performance … but never prevent the kernel from
unfolding" [L5]. **[checked]**

**Searches.** `kabstract` instantiates unknowns, then walks the term as written. Only
subterms with the pattern's `HeadIndex` and number of arguments are compared with `isDefEq`.
Subterms with loose bound variables are skipped. Subterms already checked without a match are
cached, so a shared subterm is visited once [L1]. `rw` runs this at `reducible` transparency;
`erw` runs it at `default` [goal-as-written.md L3, L4]. **[checked]**

**`simp` and `dsimp`.** `simp` rewrites with lemmas indexed in discrimination trees (keys at
`reducible` transparency), and its results are cached [L8]. It unfolds a definition only
when the definition is named (`simp [f]`), and then by its equation lemmas (`f.eq_1`,
`f.eq_def`), which are generated when first needed [L15]. `dsimp` "only applies theorems
that hold by reflexivity" [L11]. `maxSteps` defaults to 100,000 [L8]. **[checked; "unfolds
a definition only when named" recalled]**

**`decide`.** The tactic first requires the goal to have no unknowns or free variables
(`preprocessPropToDecide`). It then synthesises `Decidable p` for the proposition *as
written* (`mkDecide`) and reduces `Decidable.decide p` with
`withAtLeastTransparency .default <| whnf dec` [L11]:

- If that gives `true`, the proof is `of_decide_eq_true` with `rfl`. The kernel then checks
  it again by its own reduction.
- `+kernel` skips the elaborator's reduction and lets the kernel decide.
- `+native` evaluates compiled code and trusts the result as an axiom.

On failure, the error re-reduces, under `withoutModifyingState`, to name the instance that
got stuck ("After unfolding the instances …, reduction got stuck at …"). This diagnosis is
"lazy so that there is no performance impact" [L11]. **[checked]**

So Lean's `decide` never reads the proposition back unfolded. It reduces only the decision,
to weak head normal form, lazily. The instance comes from the proposition's written form, so
`y < 10` decides by `Nat.decLt`. That is the as-written choice D2522 avoids. **[inferred]**

**Printing.** Goals are shown as stored: instantiated, never reduced. Size is bounded by
display options [L6]:

- `pp.maxSteps` (5,000): "maximum number of expressions to visit, after which terms will
  pretty print as `⋯`".
- `pp.deepTerms` with a threshold of 50, replacing deep subterms with `⋯`.
- `pp.proofs` (off), replacing proofs with `⋯`.

**[checked]**

**Limits, and how they stay reproducible.**

- `maxHeartbeats` (200,000) is "maximum amount of heartbeats per command. A heartbeat is
  number of (small) memory allocations (in thousands)" [L7].
- The error says "(deterministic) timeout … maximum number of heartbeats … has been reached"
  and suggests `set_option maxHeartbeats <num>` [L7].
- `maxRecDepth` defaults to 1,000 [L7].
- Both are *runtime exceptions*. `Core.tryCatch` rethrows them (`if ex.isInterrupt ||
  ex.isRuntime then throw ex`), and only `tryCatchRuntimeEx` catches them [L9]. So a
  `first | tac1 | tac2` can't quietly turn "tac1 ran out" into "use tac2". Running out fails
  the command.

Heartbeats are deterministic for a given build of Lean, but they are a shared budget across
the whole command, so where the budget runs out depends on everything before it. Lean accepts
that, because running out is only ever an error. **[checked; last sentence inferred]**

### 2.2 Rocq

**Opacity, at several levels** [R2]:

- *Sealed*: `Qed` theorems are never unfolded.
- *Changeably opaque*: `Opaque` and `Transparent`. "Conversion tactics such as `simpl` and
  `unfold` only unfold transparent constants", but unification "may unfold changeably opaque
  constants".
- `Strategy`: integer levels and `expand`. When two different head constants are compared,
  "the one with lower level is expanded first". In conversion, `Opaque` is "merely a hint to
  unfold this constant last".

So opacity in Rocq is a preference for the order of unfolding, and only tactics treat it as
a ban. **[checked]**

**Lazy conversion.** Optional heuristics choose which side to unfold:

- "Kernel Conversion Dep Heuristic" prefers the constant that depends on the other.
- "Kernel Conversion Height Heuristic" uses "the definitional height … the maximum number of
  constants that need to be unfolded in the definition of c to arrive at a term with no
  constants left to unfold … always computed by the kernel when a constant is defined"
  (`Print Height`) [R2].

**[checked]**

**Reduction tactics** [R2]:

- `lazy` is call-by-need "with sharing of reductions"; `cbv` evaluates arguments first.
- `vm_compute` and `native_compute` "first normaliz[e] the terms before comparing them" and
  "ignore `Opaque` markings".
- `simpl` "reduces a term to something still readable instead of fully normalizing it". It
  "unfolds constants only if they lead to an ι-reduction" and refolds recursive calls by
  name.
- `Arguments` refines this per definition [R4]:
  - `simpl never`: not unfolded in head position.
  - `simpl nomatch`: not unfolded "if it would expose a `match` construct in the head
    position".
  - `!n`: unfold only if `n` is a constructor.
  - `/`: unfold only when applied to enough arguments.

`simpl nomatch` is Lean's smart unfolding, and Stitchwort's "keep the call whose case is
stuck", as a per-definition switch. **[checked]**

**Searches.** As written: first match in depth-first order, optionally keyed ("The subterms
… must start with the same key … and the arguments are then unified up to full reduction")
[R1]. ssreflect requires syntactically equal heads and takes patterns and occurrence
switches [R3]. **[checked, as in goal-as-written.md §3]**

**Type classes.** "`Typeclasses Opaque` … useful to declare constants which should never be
unfolded during proof search, like fixpoints or anything which does not look like an
abbreviation" [R6]. For `auto`, "Marking definitions as Hint Opaque reduces the number of
matches, but it may cause some proof searches that previously worked to fail" [R7]. Like
Lean's `instances`, this is a separate, lower transparency for speculative search.
**[checked]**

**Printing and limits.** `Printing Depth` (50): "Beyond this depth, display of subterms is
replaced by dots" [R5]. `Timeout n` is in seconds of wall-clock time, so not reproducible.
`AllocLimit` counts allocated words, and needs `memprof-limits` [R5]. **[checked]**

### 2.3 Agda

**`abstract` and `opaque`.**

- Abstract definitions "behave like postulates" outside their block [A7].
- `opaque` blocks are the same, but "opacity can be selectively controlled at use-sites" by
  `unfolding` clauses [A8].
- Opaque definitions are "a mechanism for controlling unfolding of Agda definitions, to help
  with both goal readability and performance", and "based on the theory introduced by
  Gratzer et. al." [A8].

Both are per-declaration annotations. Nothing is opaque by default. **[checked]**

**Reduction levels.** `Reduce.hs` has `instantiateFull` (unknowns only), `reduce` (weak head
normal form), `simplify` ("Only unfold definitions if this leads to simplification which
means that a constructor/literal pattern is matched") and `normalise` [A6]. **[checked]**

**Printing.** "By default, terms and types printed by interactive commands will be simplified
… only those functions that match on a constructor pattern or a projection copattern will be
reduced … `id 42` will be printed as is". `C-u` gives the term as written, `C-u C-u` the
normal form, `C-u C-u C-u` the weak head normal form [A3]. **[checked]**

**`with` and `rewrite`.** These are the one place Agda normalises in full: "The generalisation
step of a with-abstraction needs to normalise the scrutinee and the goal and argument types to
make sure that all instances of the scrutinee are generalised". The manual lists "the
normalised form of the goal and argument types are big" as a cost [A1]. Its remedy is to use
`using` instead, which "does not perform any abstraction" and "can make it much cheaper …
in situations where the goal type and context are big and expensive to normalise" [A1].
**[checked]**

Agda has eta for records by default and translates record patterns into projections [A5, A9].
So Agda's `with` is today's Stitchwort `match`, under record eta: the same blowup, documented,
with no bound. **[inferred]**

**Limits.** The conversion checker's syntactic shortcut can be given "`N` units of fuel …
successful uses of the shortcut do not affect the amount of fuel" [A4]. There are depth
limits for instance search (500) and inversion (50) [A4]. No time or allocation limits.
**[checked]**

### 2.4 Idris 2

**Glued values.** `Glued` holds a lazily computed term and a lazily computed normal form
(`MkGlue … (Core (Term vars)) (… -> Core (NF vars))`; `glueBack` reads the term back with
`clearDefs`, inline definitions only) [I5]. **[checked]**

**Opacity by visibility.** A name in another namespace reduces only if it is `public export`:
`reducibleIn nspace (NS ns (UN n)) Export = isParentOf ns nspace`, and the same for
`Private` [I3]. This is per-declaration opacity, and it is the default, without annotation:
plain `export` hides the definition's body from other modules' type checking. **[checked]**

**Evaluator limits** (`EvalOpts`) [I1]:

- `fuel : Maybe Nat -- Limit for recursion depth`. When it runs out, "Recursion depth limit
  exceeded" is logged and the call is returned as it is (`pure def`).
- `reduceLimit : List (Name, Nat)`, per-name limits: "Function … past reduction limit", and
  again the call is kept.
- `holesOnly`, `argHolesOnly`, `tcInline`: modes that unfold only meta solutions, or only
  `%tcinline` definitions (for totality checking).

**[checked]**

**Meta solutions** [I2, I5]. `Unify.idr` reads back a meta's solution as
`quoteOpts (MkQuoteOpts False False (Just nfThreshold)) empty env tmnf`, where `empty` is the
definitions with only inline definitions kept (`clearDefs`). `Quote.idr` decrements
`sizeLimit` at each application and throws "Size limit exceeded" at zero. Unify catches that
and falls back to `quote defs env tmnf`, the full read-back. The threshold is
`%nf_metavar_threshold`, "the maximum number of stuck applications allowed while unifying a
meta. The default value is 25" [I4].

This is the nearest thing to D1280 anywhere: a read-back folded by default, with a size count
that switches strategy. But it is the other way round. Idris 2 reads back folded and unfolds
everything when the folded form is *too large*; Stitchwort reads back unfolded and keeps the
call when the unfolding is too large. The limit counts applications along the read-back (it
is passed down, not shared), so it depends on the term's shape, not on the order of work.
**[checked; comparison inferred]**

**`%unbound_implicits`** controls whether lowercase names in types become implicit
arguments [I4]. It has nothing to do with unfolding. **[checked]**

**Search time.** `%search_timeout` (1,000 ms) and `checkTimer` in the evaluator are wall-clock
time [I1, I4], so not reproducible. **[checked]**

### 2.5 smalltt and the elaboration zoo

smalltt is Kovacs's demonstration of glued evaluation [K1]:

- "the first value is always the *least reduced* available version, and the second one is
  potentially more reduced". The original "is usually smaller, hence better for printing and
  meta solutions".
- Conversion has three states. *Rigid*: "Whenever we have the same top-level head symbol on
  both sides, we try to unify the spines in 'flex' mode", and unfold if that fails. *Flex*:
  cannot solve metas. *Full*: "always immediately unfold any defined symbol". This is "bounded
  approximation: it only performs limited speculation, and switches to full reductions on
  failure".
- Meta solutions: "top definitions are *never* unfolded in any meta solution, but we check
  validity up to full beta-reduction". Flex-mode quotation returns a term and a flag, with an
  `Irrelevant` placeholder for a variable that is out of scope but might vanish on
  unfolding. Full mode checks without building anything.
- Its stated limit: "we can only suspend top-level unfoldings, and local let-s and immediate
  local beta-redexes are always computed". That is Stitchwort's position too: `let`s are
  inlined on read-back (bounded-readback.md §1.2).

**[checked]**

I didn't read the elaboration zoo's code for this study. smalltt is its glued, performance
oriented descendant.

### 2.6 cooltt and Narya

**cooltt** implements "Controlling unfolding in type theory" (Gratzer, Sterling, Angiuli,
Coquand, Birkedal [G1]): "definitions are not unfolded by default, and users can unfold them
selectively and locally", to address "brittle proofs and very large proof goals". It is
elaborated into extension types in the core. Agda's `opaque` is a version of it done only in
the elaborator [A8]. This is the far end of the design space: opaque everywhere, unfold by
request. **[checked, from the abstract]**

**Narya**: not studied. I found nothing on its unfolding control in the time available.

### 2.7 Papers

- Kovacs's smalltt README [K1] is the main written account of glued evaluation and
  approximate conversion. I know of no separate paper on it. **[recalled]**
- Gratzer et al. [G1], above.
- The brief also named "lazy evaluation and delimited control" (Garcia, Lumsdaine and Sabry,
  POPL 2009). It gives a semantics of call-by-need through delimited control, not a way to
  bound unfolding in an elaborator. It isn't directly relevant, beyond confirming that
  laziness with sharing (Rocq's `lazy`) does no more work than call-by-name. **[recalled]**
- The Lean metaprogramming book's chapter on `MetaM` [L14] covers transparency, `whnf` and
  `instantiateMVars`.

## 3. Lessons for bounded-readback.md

### 3.1 The diagnosis is confirmed

Lean and Agda both have rule 2: a match on an unknown record steps through projections [L3,
A5]. Lean has no blowup because no elaborator site reads back unfolded. Agda's one site that
does (`with`) has the blowup, and the manual warns about it [A1]. So the trouble is not rule
2 but the unfolded read-backs, which is the note's §1.3 and D2514. **[inferred]**

### 3.2 Which parts each system confirms, contradicts or improves

| Note's part | Confirmed by | Contradicted by | Improved on by |
|---|---|---|---|
| Searches as written first (goal-as-written.md, §4.3) | Lean `kabstract`, Rocq keyed `rewrite`, ssreflect | Agda and Idris 2 normalise first, and Agda documents the cost | Lean caches subterms that didn't match, so shared ones are visited once [L1] |
| §4.2 the reader opens a call only if the answer could be inside | smalltt's flex then full quotation; Lean's lazy delta (arguments first, then unfold) | — | Rocq and Lean compute definitional heights once per definition, in the kernel [R2, L5]: a ready-made home for the "heads" rule's reachability |
| §4.1 cap as a function of the call alone | Nobody does this. Idris 2's threshold and fuel are the nearest, and depend on position (§2.4) | Lean, Rocq and Agda don't cap size at all; they use transparency | — |
| Zonk folded, unfolding only calls holding an unsolved unknown (`unfold_where`) | Lean `instantiateMVars`; Idris 2 folded meta read-back; smalltt never unfolds meta solutions | — | smalltt checks scope up to unfolding *without* unfolding the term (§4, S5) |
| Output terms folded (§2.5, §6) | Lean, Rocq, Agda: elaborated terms are never normalised for output | — | — |
| Messages via `small(v, 10,000)`, the note left out if too large | Lean `pp.maxSteps` 5,000, Rocq `Printing Depth` 50: printing is capped | — | Both **elide with `⋯`** and keep the message (S2) |
| `decide`: unfolded and unglued if small, else as written (D2522) | Lean `decide +kernel`: the kernel's own reduction | Lean decides the proposition **as written**, by `whnf` of the decision only | Lean names the stuck instance, lazily, on failure only [L11] |
| No per-proof syntax to lift the cap (D2529) | — | Lean `set_option maxHeartbeats N in`, Rocq `with_strategy`, Agda `unfolding` clauses: everyone has an escape hatch | — |
| No opacity annotations | — | Every system has them; Lean and Idris 2 set some by default | Rocq's `simpl nomatch` and Lean's smart unfolding are Stitchwort's `matches_at_once` as a rule, not an annotation |

### 3.3 Does anyone use a fixed node-count cap like our 100,000?

Not for searching or unifying, in Lean, Rocq or Agda. They decide what may unfold by
transparency (a property of the definition and the tactic) and keep every operation lazy, so
a large unfolding is never built. They have work limits too, but hitting one is an error, not
a different answer:

- Lean: `maxHeartbeats`, and `simp`'s `maxSteps` of 100,000 steps of rewriting (the same
  number as our cap, by coincidence).
- Rocq: `Timeout` and `AllocLimit`.

**[checked]**

Idris 2 is the exception: its size limit of 25 on meta solutions changes the result, and so
do `fuel` and `reduceLimit`, which keep the call [I1, I2]. These differ from D1280 in two
ways: they are per-path depth or count limits, not a per-call size, and they are tuned small.
**[checked; inferred comparison]**

Node caps on *display* are standard: Lean's `pp.maxSteps` is 5,000 and `pp.deepTerms` is 50
deep; Rocq's `Printing Depth` is 50. **[checked]**

So the 100,000 cap has no direct precedent. It is defensible for the reason D1280 gave: it
keeps D484's no-regression promise, which none of the others make. They promise less: Lean's
`rw` simply doesn't see inside definitions. **[inferred]**

### 3.4 Does anyone need per-declaration opacity annotations?

Yes, every system studied:

- **Lean:** five statuses, set by attribute, with defaults chosen by how the definition was
  made (instance, well-founded recursion) [L12, L13].
- **Rocq:** `Qed`, `Opaque`, `Strategy`, `Arguments … simpl never/nomatch`, `Typeclasses
  Opaque` [R2, R4, R6].
- **Agda:** `abstract`, `opaque … unfolding` [A7, A8].
- **Idris 2:** `export` against `public export`, `%inline`, `%tcinline` [I3, I4].
- **cooltt:** everything opaque unless unfolded [G1].

**[checked]**

Two of these are defaults with no annotation, and they are the most relevant to Stitchwort:

- **By how the definition is made.** Lean's well-founded functions are irreducible because
  unfolding them exposes the well-founded recursion machinery, which is large and useless to
  look at. Rocq's height heuristics are similar: computed, not written. Stitchwort could
  infer a status the same way without asking users (S3).
- **By module boundary.** Idris 2 `export`. Stitchwort's `opaque` keyword (opaque-definitions.md)
  already covers the explicit case. Not proposed here.

What Stitchwort avoids is the *need* to annotate in order to stay fast. With D484's promise
(searches see through definitions), the cap does the job annotations do elsewhere, and does
it automatically. That's the trade the note makes, and nothing here says it's wrong. But
every other system found annotations necessary sooner or later, if only as an escape hatch
(§3.6). **[inferred]**

### 3.5 Keeping results the same from run to run

Three designs in the wild:

1. **Deterministic work counters that only fail** (Lean heartbeats, allocation counts). They
   are reproducible for one build of the system. Running out is a "runtime exception" that
   ordinary `try` won't catch [L9], so it can't steer which alternative succeeds. The budget
   is shared across a command, so the place it runs out depends on order, but since running
   out always fails, that doesn't matter. **[checked]**
2. **Wall-clock timeouts** (Rocq `Timeout`, Idris 2 `%search_timeout`). Not reproducible, and
   accepted as such. **[checked]**
3. **Per-path limits that change the result** (Idris 2 fuel, `reduceLimit`, size limit).
   These are reproducible because they are passed down the recursion, not shared, so the
   result depends only on the term. **[checked; inferred that they are reproducible]**

D1280's rule is a stronger form of (3): the decision depends only on the call. That is better
than any precedent, and the note should keep it. The risk the precedents point to is (1)'s
lesson. Today a read-back that runs out at 10,000,000 nodes is recoverable
(`undo.rs:126`, bounded-readback.md §1.3), and some sites swallow it with `.ok()`. If an
`E-RESOURCE` that has been recovered from can make a later search take a different branch,
results again depend on where a shared budget ran out. That is exactly what D1280 ruled out
for the cap. **[inferred]**

### 3.6 Escape hatches

Every system lets a user go past its default limit for one proof:

- **Lean:** `set_option maxHeartbeats N in`, `unfold f`, `simp only [f]`, `erw`,
  `with_unfolding_all`.
- **Rocq:** `with_strategy`, `Transparent`.
- **Agda:** `unfolding` clauses.
- **Idris 2:** pragmas.

D2529 relies on `rewrite f` or `f.unfold` (still open as D1433, goal-as-written.md) as the
way into a large call. Precedent says that kind of escape is needed. It doesn't say a numeric
setting is. **[inferred]**

## 4. Suggested changes to the note

Each is a suggestion for Matt's decision, with its trade-off. None changes the design's core
(D2519, D2520).

**S1. In §4.3 and D2522, record Lean's `decide` as the as-written alternative, and consider
deciding by lazy evaluation instead of read-back.** Lean never reads the proposition back. It
reduces the decision `Decidable.decide p` to weak head normal form [L11]. Stitchwort's
`decide` reads the proposition back unfolded only in order to evaluate it again with gluing
off (§2.6). An evaluation of the decision procedure on the glued value with unfolding forced
(the evaluator's "unglued" mode on values, not on a read-back term) would avoid the
read-back altogether.

- *Gain:* no `small(prop, CAP)` and no read-back of the proposition, so no size question for
  `decide` at all.
- *Cost:* it needs the evaluator to run a value with gluing off in place. That may not
  exist, and I didn't check. And the instance choice must stay today's, so the decision
  still has to be *found* on the unfolded proposition; this only helps once it is found.
- *Recommendation:* mention it in D2522 as a later option. Stage 7 as written is fine.

**S2. In §4.3 (messages), elide instead of dropping.** `small(value, NOTE_CAP)` returning
`None` drops the note. Lean and Rocq keep the message and print `⋯` past 5,000 nodes or depth
50 [L6, R5]. A read-back that stops at `NOTE_CAP` nodes and writes `⋯` for what's left (or
the folded call, which is better still and is what the capped normal form would keep) gives
a note that points at the difference even when one side is large.

- *Gain:* errors in trip-journal-sized goals still say where the sides differ.
- *Cost:* a new read-back mode, and a `⋯` in snapshots when a side is large.
  `first_difference_note` needs care: a difference inside the elided part must not be
  reported as "no difference".
- *Recommendation:* yes, in stage 5. It fits the stage's size estimate.

**S3. In §4.2, compute the "heads" rule's reachability as a stored fact per definition, like
Lean's and Rocq's definitional height.** Both kernels compute a number per definition when it
is added [L5, R2]. The note computes reachability "once per definition and cached". Making it
a field of the definition, filled in when it's checked, means every declaration and every
module that loads it shares the result.

- *Gain:* no per-declaration warm-up; the rule's cost is near zero after loading.
- *Cost:* a field in the definition table. If it goes into the cached module format, the
  format changes (migration cost doesn't count). Reachability sets can be large: a height or
  a Bloom filter would be smaller but approximate. Over-approximation is safe for this rule,
  since it only skips.
- *Recommendation:* decide in stage 3, after it measures whether the heads rule pays.

**S4. In §4.2, memoise the reader on shared values, as `kabstract` does.** Lean caches
subterms already checked without a match, so a shared subterm is visited once [L1]. The note
says (§1.2) that the read-back writes each shared value out at every use, so size multiplies
with every helper that uses its argument twice. The reader, walking values, can memoise
"`find` found nothing in this cell" and "`mentions` is false for this cell". Then a value
shared a thousand times costs one visit.

- *Gain:* the reader's cost follows the value's *graph* size, not its *tree* size, on exactly
  the trip-journal shape.
- *Cost:* a map per question. Exactness is kept, because only negative answers are memoised,
  as in `kabstract`, and a positive `find` must be walked again to keep the pre-order count.
- *Related, and not recommended:* measuring `CAP` itself by graph size. It would make the cap
  depend on sharing, which depends on how the evaluator happened to build the value, and
  that weakens D1280's "function of the call alone".
- *Recommendation:* yes, in stage 3.

**S5. In §4.3 (zonk), note smalltt's alternative to `unfold_where`, and why the note doesn't
take it.** smalltt never unfolds a meta solution: it checks it up to full unfolding and puts
an `Irrelevant` placeholder where a variable is out of scope but vanishes on unfolding [K1].
The note's `unfold_where` unfolds the calls instead.

- *Gain of smalltt's way:* solutions stay folded everywhere.
- *Cost:* Stitchwort's kernel checks every term, and an `Irrelevant` placeholder isn't a
  term it can type.
- *Recommendation:* keep `unfold_where`, and add a sentence saying why, so a reviewer who
  knows smalltt doesn't ask.

**S6. In §1.3 or §5, decide that a recovered `E-RESOURCE` never chooses between
alternatives.** Lean's rule [L9] is that running out of a limit can't be caught by the
ordinary `try`. After stage 6, the 10,000,000 limit should almost never be reached from the
sites in §2. Where it still is, the note could say that the declaration fails, rather than
the error being undone and a different path taken.

- *Gain:* reproducibility doesn't depend on a shared budget, completing D1280's principle.
  Errors also become cheaper, with no second attempt after ten million steps.
- *Cost:* declarations that recover today, slowly, would fail. Stage 0 can count them
  (`undo.rs:126` paths that catch `E-RESOURCE`). There may be none on `main`.
- *Recommendation:* add it as a question for stage 0 to answer, not yet a decision.

**S7. In D2529, cite the precedent.** Every system has a per-proof escape (§3.6). The note's
answer (`rewrite f`, `f.unfold`) is an escape of the "unfold this by name" kind, which Lean
(`unfold`, `simp only [f]`) and ssreflect (`rw /f`) also have. It is worth saying that this
is why no numeric setting is needed, and that D1433 is what D2529 depends on. *Cost:* none.

**S8. Optional, outside this note: an inferred "abbreviation" status.** Rocq's `Arguments f
/` and Lean's `@[reducible]` mark definitions that should always unfold. Stitchwort could
infer that status (non-recursive, no `case`, small body) and let the keyed searches see
through such definitions in the as-written pass, before the fallback.

- *Gain:* fewer fallbacks to `find` on the capped normal form.
- *Cost:* a new rule for what "as written" means, which goal-as-written.md decided against
  implicitly.
- *Recommendation:* a backlog idea, not part of SW-1712's stages.

## 5. What this study did not do

- It ran nothing, so the suggestions' gains are not measured.
- It did not read Narya, redtt or the elaboration zoo's code. Rocq's evar normalisation, Lean's
  `instantiateMVars` internals and Agda's `from-yes` lemmas are marked [recalled].
- It did not revisit `rewrite` and `match` prior art, which goal-as-written.md §3 covers with
  sources.
- It did not check whether Stitchwort's evaluator can run a value with gluing off in place
  (S1).

## 6. Sources

Read on 6 November 2026, from each project's default branch.

- [L1] Lean 4, `src/Lean/Meta/KAbstract.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean>
- [L2] Lean 4, `src/Lean/Meta/Tactic/Rewrite.lean`: <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean>
- [L3] Lean 4, `src/Init/MetaTypes.lean` (`TransparencyMode`, `EtaStructMode`) and `src/Lean/Meta/WHNF.lean` (`toCtorWhenStructure`, smart unfolding, `smartUnfoldingReduce?`): <https://github.com/leanprover/lean4/blob/master/src/Init/MetaTypes.lean>, <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/WHNF.lean>
- [L4] Lean 4, `src/Lean/Meta/ExprDefEq.lean` (`isDefEqDelta`, `unfoldBothDefEq`, `tryHeuristic`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/ExprDefEq.lean>
- [L5] Lean 4, `src/Lean/Declaration.lean` (`ReducibilityHints`, definitional height): <https://github.com/leanprover/lean4/blob/master/src/Lean/Declaration.lean>
- [L6] Lean 4, `src/Lean/PrettyPrinter/Delaborator/Options.lean` (`pp.maxSteps`, `pp.deepTerms`, `pp.proofs`): <https://github.com/leanprover/lean4/blob/master/src/Lean/PrettyPrinter/Delaborator/Options.lean>
- [L7] Lean 4, `src/Lean/CoreM.lean` (`maxHeartbeats`, `throwMaxHeartbeat`, `maxRecDepth`): <https://github.com/leanprover/lean4/blob/master/src/Lean/CoreM.lean>
- [L8] Lean 4, `src/Init/MetaTypes.lean` (`Simp.Config`, `defaultMaxSteps := 100000`) and `src/Lean/Meta/Tactic/Simp/Types.lean` (cache): <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/Types.lean>
- [L9] Lean 4, `src/Lean/CoreM.lean` (`Core.tryCatch`, `tryCatchRuntimeEx`) and `src/Lean/Exception.lean` (`runtime.maxRecDepth`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Exception.lean>
- [L10] Lean 4 metaprogramming book, and `src/Lean/MetavarContext.lean` for `instantiateMVars` (not re-read; recalled): <https://github.com/leanprover/lean4/blob/master/src/Lean/MetavarContext.lean>
- [L11] Lean 4, `src/Lean/Elab/Tactic/Decide.lean` (`evalDecideCore`, `doElab`, `doKernel`, `diagnose`) and `src/Init/Tactics.lean` (docstrings of `decide`, `dsimp`, `unfold`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Tactic/Decide.lean>, <https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean>
- [L12] Lean 4, `src/Lean/ReducibilityAttrs.lean` (`ReducibilityStatus`): <https://github.com/leanprover/lean4/blob/master/src/Lean/ReducibilityAttrs.lean>
- [L13] Lean 4, `src/Lean/Elab/PreDefinition/Mutual.lean` (`addPreDefAttributes`): <https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/PreDefinition/Mutual.lean>
- [L14] Lean 4 metaprogramming book, "MetaM" (transparency, `whnf`, `reduce`, `instantiateMVars`): <https://leanprover-community.github.io/lean4-metaprogramming-book/main/04_metam.html>
- [L15] Lean 4, `src/Lean/Meta/Eqns.lean` (equation lemmas realised lazily): <https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Eqns.lean>
- [R1] Rocq reference manual source, `doc/sphinx/proofs/writing-proofs/equality.rst` (`rewrite`, `Keyed Unification`): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/writing-proofs/equality.rst>
- [R2] The same file, sections on reduction tactics (`lazy`, `cbv`, `simpl`, `cbn`, `vm_compute`, `native_compute`), "Controlling reduction strategies" (`Opaque`, `Transparent`, `Strategy`, `with_strategy`) and the conversion heuristics flags.
- [R3] Rocq reference manual source, `doc/sphinx/proof-engine/ssreflect-proof-language.rst`: <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proof-engine/ssreflect-proof-language.rst>
- [R4] Rocq reference manual source, `doc/sphinx/language/extensions/arguments-command.rst` ("Effects of Arguments on unfolding"): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/language/extensions/arguments-command.rst>
- [R5] Rocq reference manual source, `doc/sphinx/proof-engine/vernacular-commands.rst` (`Timeout`, `AllocLimit`, `Printing Depth`): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proof-engine/vernacular-commands.rst>
- [R6] Rocq reference manual source, `doc/sphinx/addendum/type-classes.rst` (`Typeclasses Opaque`): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/addendum/type-classes.rst>
- [R7] Rocq reference manual source, `doc/sphinx/proofs/automatic-tactics/auto.rst` (`Hint Opaque`): <https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/automatic-tactics/auto.rst>
- [A1] Agda user manual, "With-Abstraction" (generalisation, performance considerations, `using`): <https://agda.readthedocs.io/en/latest/language/with-abstraction.html>
- [A2] Agda, `src/full/Agda/TypeChecking/With.hs` (`normalise vtys`): <https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/With.hs>
- [A3] Agda user manual, "Emacs Mode" (normalisation levels of displayed terms): <https://agda.readthedocs.io/en/latest/tools/emacs-mode.html>
- [A4] Agda user manual, "Command-line options" (`--syntactic-equality`, `--instance-search-depth`, `--inversion-max-depth`, `--termination-depth`): <https://agda.readthedocs.io/en/latest/tools/command-line-options.html>
- [A5] Agda, `src/full/Agda/TypeChecking/RecordPatterns.hs`: <https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/RecordPatterns.hs>
- [A6] Agda, `src/full/Agda/TypeChecking/Reduce.hs` (`instantiateFull`, `reduce`, `simplify`, `normalise`): <https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/Reduce.hs>
- [A7] Agda user manual, "Abstract definitions": <https://agda.readthedocs.io/en/latest/language/abstract-definitions.html>
- [A8] Agda user manual, "Opaque definitions": <https://agda.readthedocs.io/en/latest/language/opaque-definitions.html>
- [A9] Agda user manual, "Record types" (eta-equality, record patterns): <https://agda.readthedocs.io/en/latest/language/record-types.html>
- [I1] Idris 2, `src/Core/Normalise/Eval.idr` (`fuel`, `reduceLimit`, `evalDef`, `checkTimer`) and `src/Core/Value.idr` (`EvalOpts`): <https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise/Eval.idr>, <https://github.com/idris-lang/Idris2/blob/main/src/Core/Value.idr>
- [I2] Idris 2, `src/Core/Unify.idr` (meta solution read-back with `nfThreshold`, fallback to `quote`): <https://github.com/idris-lang/Idris2/blob/main/src/Core/Unify.idr>
- [I3] Idris 2, `src/Core/Context.idr` (`reducibleIn`, `clearDefs`): <https://github.com/idris-lang/Idris2/blob/main/src/Core/Context.idr>
- [I4] Idris 2 documentation, "Pragmas" (`%nf_metavar_threshold`, `%search_timeout`, `%auto_implicit_depth`, `%unbound_implicits`, `%tcinline`): <https://github.com/idris-lang/Idris2/blob/main/docs/source/reference/pragmas.rst>
- [I5] Idris 2, `src/Core/Normalise.idr` (`Glued`, `glueBack`, `glueClosure`) and `src/Core/Normalise/Quote.idr` (`QuoteOpts`, `sizeLimit`): <https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise.idr>, <https://github.com/idris-lang/Idris2/blob/main/src/Core/Normalise/Quote.idr>
- [K1] András Kovács, smalltt README (glued evaluation, rigid/flex/full, meta solutions): <https://github.com/AndrasKovacs/smalltt>
- [G1] D. Gratzer, J. Sterling, C. Angiuli, T. Coquand, L. Birkedal, "Controlling unfolding in type theory", arXiv:2210.05420; MSCS 35 (2025): <https://arxiv.org/abs/2210.05420>

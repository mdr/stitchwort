# Productivity features Stitchwort could borrow from other languages

Research and recommendations, 1 November 2026.

Stitchwort has already borrowed much of the useful surface of modern functional languages. The next substantial gains look less like adding another collection of operators and more like making types, effects and proofs do more work for the programmer.

My strongest recommendations are to develop **type-directed editing**, **an explanation view for elaboration and proof search**, **a convenient syntax for passing blocks to handlers**, and **generated principles for reasoning about functions**. The most interesting longer-term direction is **restricted, inspectable metaprogramming**: users should eventually be able to generate routine definitions and proofs without modifying the Rust compiler. Proof-carrying views and domain-specific test generators are promising library experiments before that larger investment.

The rankings below are design judgments, not measured productivity improvements. Features described as proposed, and all code blocks marked `text`, are sketches rather than accepted Stitchwort syntax. Existing Stitchwort examples are identified separately.

## 1. Priorities

Cost means likely engineering scope: **small** is a localized addition; **medium** crosses a few compiler/tooling subsystems; **large** needs a sustained design and implementation effort. It is not an estimate in days. Even features that leave the kernel unchanged need careful elaboration, diagnostics and source mapping.

| Priority | Borrow | Main precedents | Why it matters here | Scope | Recommendation |
|---|---|---|---|---|---|
| 1 | Generate cases, introduce parameters, refine holes | Idris, Agda, GHC, rust-analyzer | Turn precise types into useful editing actions | Medium, tooling/elaborator | Extend existing goal actions |
| 2 | Explain inferred arguments, constraints and proof search | Lean, GHC, Elm, rust-analyzer | Make an otherwise opaque failure repairable | Medium, tooling/elaborator | Start with one compact explanation command |
| 3 | Block arguments and handler scope sugar | Koka, Swift; OCaml binding operators | Remove nested thunk punctuation in ordinary programs | Medium, parser/elaborator | Design and compare two narrow forms |
| 4 | Function-specific cases, equations and induction | Rocq Equations, Lean | Avoid reproducing a function's branching in its proofs | Medium to large, generation | Advance existing work, rather than create a new initiative |
| 5 | Pure watches and inspectable pipeline results | Unison | Shorten the edit, run, inspect loop | Medium, tools/runtime | Prototype as an explicit editor action |
| 6 | Generators that build valid inputs and action sequences | Hypothesis, QuickCheck family | Exercise meaningful states, not mostly rejected inputs | Medium, test library/tooling | Use existing test machinery; pilot on Rogue |
| 7 | Proof-carrying views | F# active patterns, Agda views/with | Expose a useful decomposition and the facts that justify it | Small library pilot; medium sugar | Try without syntax first |
| 8 | Reusable deriving through explicit equivalences | Haskell deriving via, Scala derivation | Reduce boilerplate without discarding interface laws | Small library pilot; large general mechanism | Start with law-preserving transport functions |
| 9 | Abstract construction boundaries | OCaml abstract/private types, Rust modules | Make smart-constructor invariants true for all public values | Large language/tooling design | Worth a separate design, beyond file privacy |
| 10 | User-defined generation and proof-producing procedures | Lean, Idris, Agda, Swift | Let libraries extend productivity without compiler patches | Large architectural work | Stage through inspection and external generation |

The first four would be my initial shortlist. Watches and generators are good parallel product experiments. The later items are valuable directions, but they need evidence from real use before becoming general language mechanisms.

## 2. What Stitchwort already has

This review started at commit `62a65a92a824a9655f920c63b3b3a5db30d0a03d`. The repository was receiving concurrent changes, so this is a dated assessment rather than a claim about every later commit.

The current [syntax reference](../syntax.md), implementation and examples take precedence over old comparison prose. In particular, [compared.md](../compared.md) still describes several features as absent that are now implemented.

| Tempting suggestion | Current position | Useful remaining question |
|---|---|---|
| Pipes, terse lambdas and operator sections | Built, including method sections and sections spanning expressions | Are multiline callbacks and handler scopes pleasant? |
| Named/default arguments | Built, including signature defaults in the syntax reference | Improve discovery and completion; don't propose them anew |
| Immutable records and updates | Built, including dependent-field restrictions and shared variant fields | Would nested updates save enough repetition? |
| Automatic equality, ordering and printing | Built, with generated laws and explicit limitations | Can users define additional derivations? |
| Enumerate finite types and decide closed statements | `Finite`, derived instances, `Finite.check`, `byDecision` | Better APIs for finite tables and generated valid test data |
| Equational proofs and arithmetic automation | `calc`, `rewrite`, `omega`, `ring`, `cases` | Inspect what they used; add solvers only for demonstrated gaps |
| Type-directed search and editor proof suggestions | `search --at` and goal quick fixes already exist | Partial refinements, case generation, reliable latency |
| Typed holes and live goals | Built for programs and proofs | Use the goal as a starting point for edits |
| Counterexample and property testing | Built; theorem auditing too | Richer valid inputs, meaningful coverage and stateful tests |
| Direct-style effects and comprehensions | Abilities, handlers, `Fail`, `Abort`, `Each` | Simplify handler calls, not introduce a second effect notation |
| Well-founded recursion | `decreasing`, lexicographic pairs, `attach`, unfold lemmas | Explain termination failures and derive proof structure |
| Nominal wrappers with cheap representations | Microtypes via one-field records and unboxing | Construction privacy and reusable law-preserving derivation |

These are grounded in [syntax.md](../syntax.md), [the guide](../guide/README.md), [the LSP server](../../crates/cli/src/lsp.rs), [derivation code](../../crates/elab/src/derive_induct.rs), and the relevant proposals' “As built” sections. The server currently advertises parameter-name completion and goal quick fixes; that is more than syntax colouring, but less than general expression completion or structural editing.

The design constraints worth retaining are programming first, totality visible in types, checking that never performs program effects, ordinary source files, and a small kernel. [DESIGN.md](../../DESIGN.md) explicitly excludes a Lean-style tactic language. It also still lists editor integration as a non-goal despite the working LSP; that illustrates why design intent and implementation status must be checked separately.

Existing [literature registers](README.md) already cover elaboration, proof automation, recursion and infrastructure in depth. This report complements them with a cross-language productivity review. Where the same idea has already been researched or decided, the sections below say so.

## 3. Make the type checker an editing partner

### 3.1 Generate valid cases and useful partial programs

**Precedent.** Idris offers case splitting, missing-clause generation and expression search. Its vector example eliminates impossible branches using index information. GHC also distinguishes a complete hole fit from a refinement that introduces further holes. These are useful operations even when the system cannot synthesize an entire program. [Idris interactive editing](https://idris2.readthedocs.io/en/latest/tutorial/interactive.html), [GHC typed holes](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/typed_holes.html).

**Adaptation.** Stitchwort already shows goals and offers proofs that close a `?`. Add a small family of structural actions:

- Introduce the parameters required by the goal.
- Split a selected variable, respecting indices and impossible constructors.
- Fill missing match arms with holes.
- Refine a goal with a constructor or lemma, showing the remaining obligations.
- Turn a selected expression into a named helper with its actual dependencies.

For example, starting from this unfinished definition:

```text
def zipSame [n: Nat] (xs: Vec a n) (ys: Vec b n): Vec (a, b) n := ?
```

Splitting `xs` and then `ys` should produce only compatible empty and nonempty branches. The generated holes should show the refined indices. Users should not have to guess which combinations are impossible.

For a proof, an action might offer `Eq.cong Some ?` with the remaining equality displayed, rather than only say that it found no complete proof. This is an extension of current search, whose [stage 3 follow-up](../proposals/search.md) specifically records missing `Eq.cong` wrapping as an example.

**Fit and risk.** Excellent fit: these actions produce ordinary source that is checked normally. Case generation for dependent matches is medium work, not a text-template feature. Extracting helpers must include variables mentioned by types, preserve effects, avoid capture and retain termination evidence. An action that creates holes must be labelled a refinement; rechecking it is not a proof that the unfinished program is correct.

**First experiment.** Five representative actions over ordinary lists, `Vec`, dependent records and proofs. Measure whether the generated text is readable and how often it survives a full recheck. Expose the same operation through a CLI request with a source location, so agents receive the same benefit. For ordinary refactoring precedents, see [rust-analyzer assists](https://rust-analyzer.github.io/book/assists.html).

### 3.2 Explain what elaboration decided

Stitchwort's surface hides implicit arguments, instances, decisions, generated matches, decreasing proofs and effect rows. That is productive until one of those choices fails or differs from what the programmer expected.

The useful borrowed principle is **progressive disclosure**. GHC's hole reports can show types, provenance and extra obligations. Lean's `simp?` can report a smaller explicit invocation sufficient for a proof. Rust-analyzer offers actions that make inferred syntax explicit. [GHC hole reporting](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/typed_holes.html), [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference), [rust-analyzer assists](https://rust-analyzer.github.io/book/assists.html).

A proposed inspection result for an expression could say:

```text
expression: v.getLt i
result: Nat
implicit n: 12                     from the receiver type
required proof: i < 12
proof used: inRange                local hypothesis
abilities: none
```

On failure, explain the blocked obligation and where its expected type came from. For `decreasing`, show the recursive call, old measure, new measure and fact missing from scope. For instance search, show the few relevant candidates and why they did not apply, with deeper traces available on demand.

This should build on [navigation metadata](../proposals/code-navigation.md), [goal snapshots](../proposals/lsp-goal-holes.md), [postponed constraints](../proposals/postponement.md) and [goal readback](../proposals/goal-readback.md). A compact explanation is more useful than dumping the elaborated AST or the entire unifier log.

**Priority:** very high. An explanation command serves both humans and agents and makes future language conveniences easier to debug. Keep source-level names and expressions wherever possible; generated identifiers and fully unfolded terms are implementation details unless explicitly requested.

### 3.3 Suggest termination measures and proof evidence

Lean's `termination_by?` reports an inferred measure. Its recursion support also preprocesses selected higher-order calls so recursive callbacks can receive evidence about their arguments. [Lean recursive definitions](https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/).

Stitchwort already has the hard foundations: measures, congruence lemmas, `List.attach`, and automatic size facts for supported nested datatypes. Its [recursion literature review](inductives.md) already recommends measure suggestions and automatic attachment. This review reinforces that recommendation rather than reopening the termination design.

Start with a diagnostic or edit that proposes a measure only after checking it through the existing elaborator. If nothing succeeds, display the per-call obstacle. Automatically introducing membership evidence under callbacks is a second step: it should preserve the user's equation and keep the evidence out of ordinary source unless needed for explanation.

**Risk:** searching too many candidate measures can make the very error being explained expensive. Suggestions need strict work limits. Failing to find a measure means only that the suggestion search failed.

## 4. Reduce punctuation and repeated structure in programs

### 4.1 Block arguments and handler scopes

**Precedent.** Koka permits trailing lambdas and a `with` statement that passes the rest of a lexical scope as a callback. Swift also gives trailing closures a pleasant call syntax. OCaml binding operators expose library sequencing through a small syntax extension. [Koka book, anonymous functions and with statements](https://koka-lang.github.io/koka/doc/book.html#sec-with), [Swift closures](https://docs.swift.org/latest/documentation/the-swift-programming-language/closures/), [OCaml binding operators](https://ocaml.org/manual/5.5/bindingops.html).

The Koka idea is particularly well matched to Stitchwort. Current Rogue code includes this real expression:

```stitchwort
Terminal.simulate keys (() => Random.withSeed testSeed (() => playGame (newGame())))
```

Source: [Rogue play-through tests](../../games/rogue/src/Rogue/Tests/PlayThrough.sw).

Two alternative sketches to compare are:

```text
Terminal.simulate keys do
  Random.withSeed testSeed do
    playGame (newGame())
```

and a form that scopes over the remaining block:

```text
with Terminal.simulate keys
with Random.withSeed testSeed
playGame (newGame())
```

The token is undecided; `do` here would mean a delayed block argument, not monadic sequencing. A narrow rule for a final `() -> {e} a` argument would already cover many handlers and parser combinators. It should desugar to the existing thunk call, preserving when the body runs, how often the callee may invoke it, and the order of earlier arguments.

**Why this beats another comprehension syntax.** Direct-style effects and `Each` already cover sequencing and comprehensions. The friction here is expressing the scope over which a handler runs. A block argument also helps ordinary higher-order functions without introducing a new abstraction.

**Risk:** layout, partial application and existing `match … with`/`handle … with` forms must stay unambiguous. A block may run zero or multiple times; syntax must not imply exactly-once execution. Start with the explicitly nested form, compare readability in real programs, then decide whether rest-of-scope syntax earns its additional rule.

### 4.2 Refutable bindings and pattern guards

Rust's `let … else` keeps the successful path flat; its match syntax also has guards. These are separate conveniences, with separate semantics. [Rust concise control flow](https://doc.rust-lang.org/book/ch06-03-if-let.html), [Rust match expressions](https://doc.rust-lang.org/reference/expressions/match-expr.html).

Stitchwort already handles the common `Option` case nicely:

```stitchwort
let (c, rest) := Fail.need t.uncons "expected a turn, got nothing"
```

See [Fail and Result](../syntax.md#fail-and-result). A Rust-style `?` for propagation would overlap with that and collide with the existing goal marker. It is not a good initial addition.

The remaining case is matching a particular constructor and then continuing with its fields:

```text
let Pair left right := number else Fail.fail "expected a pair"
use left right
```

A first design could require an aborting failure branch and translate directly to `match`. A more general form where the else branch returns the enclosing block's result introduces nonlocal control flow and deserves a separate decision. The minimal version is sugar, but it is useful only if occurrences beyond `Option` are common enough.

Pattern guards could put a constructor test and a condition in one arm. In dependent code, a named successful guard should make its proof available just as `if h:` does. Arbitrary guard predicates cannot simply be treated as covering all constructors; exhaustiveness remains a real obligation.

**Recommendation:** collect actual nested constructor matches first. Lower priority than block arguments. Keep current `Fail.need`, `ensure`, `orFail` and ordinary `match` as the default idioms.

### 4.3 Nested record updates and small optics

Lenses provide composable reads and immutable updates. FSharpPlus demonstrates composition through nested records and optional/list elements. [FSharpPlus lenses](https://fsprojects.github.io/FSharpPlus/lens.html).

Stitchwort already has record updates. A real nested update in [2024 Day 9](../../aoc/src/Aoc/Year2024/Day09/Day09.sw) is:

```stitchwort
{ file | span = { file.span | start = span.start } }
```

A possible convenience is:

```text
{ file | span.start = newStart }
```

That is a more modest starting point than importing an entire optics vocabulary. Bind the base once, combine updates to a shared prefix predictably, and specify the order of effectful right-hand sides. Conflicting updates such as replacing both `span` and `span.start` should be rejected initially.

Dependent fields are the important limit: changing `items` may invalidate a later proof about its length. Existing [record-update rules](../syntax.md#records) require dependent fields to be replaced too. Nested syntax must preserve those obligations; a lens cannot silently repair an invariant.

**Recommendation:** low to medium priority. A small lawful lens library over ordinary records is possible without syntax. Add nested paths only if real application code has enough repetition. General dependent optics would be a much larger research question.

### 4.4 Typed builders without new syntax families

Kotlin's builders combine ordinary functions with receiver lambdas to describe structured data; `DslMarker` limits accidental access to outer receivers. [Kotlin type-safe builders](https://kotlinlang.org/docs/type-safe-builders.html).

The transferable idea is a fluent, typed vocabulary for constructing structured values: documents, test scenarios, parser descriptions or UI trees. Stitchwort could prototype one using ordinary records, functions and an ability whose handler collects nodes. Block arguments would make it more pleasant.

I would retain explicit operation names and lexical scope at first. Adding implicit receivers, overloaded string operators and a second set of scope rules just to obtain Kotlin's exact appearance would be poor value. A builder must also validate domain invariants; being well typed as a tree does not establish that it represents valid HTML or a valid test scenario.

**Recommendation:** library experiment when a concrete builder is wanted. No new language feature required beyond the separately useful block-argument idea.

## 5. Borrow proof structure without adopting a tactic language

### 5.1 Generate equations and induction for the function being proved

**Precedent.** Rocq's Equations package generates functional induction principles following a definition's actual branching and recursive calls. Its `half` example explains why induction on a natural number can give the wrong induction hypothesis for recursion by two. Lean also generates function-specific induction principles. [Equations tutorial](https://rocq-prover.github.io/platform-docs/equations/tutorial_basics.html), [Lean 4.8 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.8.0/).

Stitchwort should borrow the generated theorem, not require the associated tactic interface. For a function that strips two elements at a time, a useful principle would have empty, singleton and two-or-more cases, with an induction hypothesis about the actual recursive call. For an accumulator loop, it must generalize the changing accumulator. For `decreasing`, it must follow the real measure-based recursion while keeping fuel out of the public theorem.

There are three related outputs:

1. Per-branch equations suitable for rewriting.
2. A cases principle exposing conditions learned along a branch.
3. An induction principle adding hypotheses for recursive calls.

Stitchwort already generates `f.unfold` for `decreasing` definitions, and supported nested datatypes get `T.induct` and `T.inductMem`. Those are precedents, not substitutes for induction about a particular function. The implementation already admits generated ordinary theorems through the checker.

**Status:** already identified in [inductives.md](inductives.md) and [proof-automation.md](proof-automation.md); existing board items include SW-199, SW-802 and SW-809. This should advance that work, with the shared design proposed there. Calls under callbacks and mutual recursion make the general case substantial; start with a useful restricted subset and diagnose unsupported shapes explicitly.

**Acceptance target:** simplify a few proofs whose structure currently duplicates the program, including a `decreasing` function and an accumulator loop. Count helper lemmas, proof size and checking time, while reviewing whether the resulting theorem is understandable.

### 5.2 Search that can explain and export its result

Lean's `simp?` illustrates a useful distinction between discovering a proof and retaining a small explicit recipe. Isabelle's Sledgehammer work similarly emphasizes reconstruction into checkable proofs. [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference), [Sledgehammer Isar reconstruction source](https://www.isabelle.in.tum.de/library/HOL/HOL/ISABELLE_HOME/src/HOL/Tools/Sledgehammer/sledgehammer_isar.ML.html).

Stitchwort already offers source text for closing proofs and checks project suggestions. The useful next step is better presentation and minimization: distinguish a complete proof from a useful rewrite step, identify the relevant hypotheses, and omit irrelevant candidates when a short closer works.

A longer-term command could try removing unnecessary supplied facts from `omega [h1, h2, h3]` or `ring […]`, then recheck the smaller expression. An expansion view could explain a `cases` split tree or a solver certificate without making the expanded proof the default source format.

**Recommendation:** prioritize the existing [search polish](../proposals/search.md) work. Don't add a general-purpose proof-search language for this. Keep resource limits per candidate; a suggestion that blocks the editor for minutes undermines the feature.

### 5.3 Scoped simplification only when an example earns it

Lean's simplifier demonstrates the value of rewriting with a controlled lemma set. Its local `simp only` form also demonstrates a way to make a proof's dependencies explicit. [Lean tactic reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference).

Stitchwort already investigated this and deferred `simp [rules]` because the motivating examples needed Boolean case splitting, now supplied by `cases`. [simp.md](../proposals/simp.md) records that decision. A general language survey is not evidence to reverse it.

If recurring proofs now require long chains of membership, mapping or normalization lemmas that existing search cannot combine, revisit a narrow explicit-list simplifier. Require an actual corpus of such proofs. Termination of rewriting, direction selection, conditional premises and explanation of the chosen normal form are the real design work.

**Recommendation:** retain the trigger. Do not turn a globally growing rewrite database into an invisible dependency of every proof.

## 6. Improve the feedback loop for running and testing programs

### 6.1 Pure watches and pipeline inspection

Unison's watch expressions evaluate inline and cache results by expression hash. The useful interaction is immediate feedback next to the code being edited, with unchanged pure expressions reused. [Unison tour](https://www.unison-lang.org/docs/tour/).

Stitchwort has CLI evaluation, a REPL and a playground Evaluate tab already. The new opportunity is editor integration and convenient inspection of intermediate values. For example, a report beside a selected pipeline could show:

```text
parse input       => Ok [18 items]
group regions     => 7 regions
price each        => [24, 40, ...]
sum               => 1930
```

The safe initial product is **evaluate this selected closed expression**, explicitly invoked, in a separate cancellable worker with output and work limits. Reuse the actual program's bindings rather than independently reevaluating each displayed stage; effects and expensive calls make naive instrumentation misleading. Values inside a generic function need concrete supplied inputs, not guesses for local variables.

Automatic watches can follow later for pure, total, finished expressions. Even these can take a long time or produce enormous results. Type checking itself must remain separate from execution; automatic evaluation must never run `IO` or `{Partial}` just because a document opened. Handled effects are acceptable only once the resulting expression is pure and total.

A runtime result cache needs the expression's dependencies, evaluator/representation version and execution settings where relevant. It must not be confused with the existing cache of checked declarations or test outcomes.

**Recommendation:** prototype the editor action before adding a watch declaration to the grammar. This is especially useful for parser results and AoC intermediate structures. Specialized tables or grids can be renderer plugins later; plain truncated values are enough to establish value.

### 6.2 Valid-input generators and stateful model tests

Hypothesis supports custom strategies, health checks for excessive filtering and tests generated as sequences of actions. The latter is useful for comparing an implementation with a simpler state-machine model. [Hypothesis API and health checks](https://hypothesis.readthedocs.io/en/latest/reference/api.html), [Hypothesis stateful tests](https://hypothesis.readthedocs.io/en/latest/stateful.html).

Stitchwort already generates values, tests properties, searches for counterexamples and shrinks failures. The important borrowing is greater **control of the distribution** and **construction of valid states**. A test for sorted lists should generate sorted lists of useful sizes rather than discard almost every arbitrary list. A stateful test should generate commands valid in the current model state, then compare observable results and invariants after each command.

Rogue is a natural pilot: generate a small valid level and legal command sequences; run a simple reference transition and the implementation; shrink a failure to a short sequence and small level. The same technique applies to mutable-looking APIs implemented with pure state transitions and to effect handlers tested against a simple model.

The [proof-automation research](proof-automation.md) already demonstrates a false increasing-list statement missed because the generated satisfying lists were too small. It recommends recording the largest meaningful input, not just the largest attempted input. Preserve that distinction. Report accepted versus rejected cases, relevant size distributions, replay information and the shrunk counterexample.

**Fit and risk:** mainly test library and driver work. A validity-preserving shrinker must not silently destroy the precondition. Tests remain evidence; generated examples never discharge a theorem. If a generator itself constructs a proof-carrying input, that proof establishes input validity, not the property under test.

**Recommendation:** build the custom generator path on existing parameterized tests, as already anticipated in [counterexample-search.md](../proposals/counterexample-search.md). Start with one useful domain and a stable replay format; a general state-machine DSL can wait.

### 6.3 Save useful failures as regression examples

The productivity lesson from property-testing systems is that a discovered failure should remain easy to rerun. Hypothesis has explicit replay and example-database facilities. [Hypothesis API](https://hypothesis.readthedocs.io/en/latest/reference/api.html).

For Stitchwort, offer an action that turns a concrete counterexample into an ordinary named `test`, or emits a test snippet for review. Keep enough provenance to tell whether it came from a failed theorem, a property test or a runtime disagreement. A theorem statement subsequently changing must not make an old input silently mean something different.

This is a small addition after stable counterexample rendering. It is useful independently of a more advanced generator system. Automatically writing tests into project files should be an explicit action, not a side effect of checking.

## 7. Make data abstractions more useful

### 7.1 Views that carry the facts needed by proofs

F# active patterns let functions expose named decompositions of values. Agda's with-abstraction generalizes types over an intermediate computation. Indexed views make useful facts available after matching; the classic Idris tutorial demonstrates this with a parity view of natural numbers. These ideas can be combined, but they are not the same feature. [F# active patterns](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/active-patterns), [Agda with-abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html), [Idris 1 views tutorial](https://docs.idris-lang.org/en/latest/tutorial/views.html).

For Stitchwort, the most valuable version is a total view function whose result describes the input and carries equations relating the decomposition to it. An even/odd view of `n` might produce a witness `k` and a proof of either `n = 2*k` or `n = 2*k+1`. A text-prefix view might return the rest and a reconstruction equation. A nonempty-list view could expose a head and tail while preserving their relationship to the original list.

This avoids the situation where a recognizer returns only `Bool`, and every caller then needs a separate soundness lemma and manually aligned rewrites. Ordinary `match` on the view is already enough to test the API. Existing named-match equations provide another useful tool, so the pilot must show what additional burden the certified result removes.

**Recommendation:** try two library views before any active-pattern syntax. Choose ones repeatedly useful in current programs, not merely another way to match `Cons`. Preserve the original value's size evidence when recursive calls follow a decomposition; an arbitrary view is not automatically a structural decrease.

### 7.2 Pattern synonyms for recurring constructor shapes

Agda and Haskell both support names for recurring patterns. Agda expands synonyms in abstract syntax; Haskell supports a richer distinction between matching and construction. [Agda pattern synonyms](https://agda.readthedocs.io/en/latest/language/pattern-synonyms.html), [GHC pattern synonyms](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/pattern_synonyms.html).

This could help code over compiler ASTs or domain trees where a frequent shape is deeply nested. Start with transparent constructor-only expansion and readable expanded diagnostics. A bidirectional synonym should build the same shape it matches. Constructor expansion should precede the normal coverage and termination checks.

An arbitrary function used in a pattern is a different feature: it may be expensive, perform effects or fail to give useful coverage information. Use an explicit pure view call for that initially.

**Recommendation:** plausible later sugar, below the view-library experiment. The current code has some nested tree patterns, but that alone does not establish enough repeated shapes to justify a new declaration form.

### 7.3 Reuse instances through explicit equivalences

Haskell's `DerivingVia` reuses an instance through another type when methods can be safely coerced between runtime representations. Scala's derivation exposes product/sum information to user-defined derivation code. [GHC deriving via](https://ghc.gitlab.haskell.org/ghc/doc/users_guide/exts/deriving_via.html), [Scala type class derivation](https://docs.scala-lang.org/scala3/reference/contextual/derivation.html).

Stitchwort's interfaces can include laws. Reusing an operation without transporting its laws is insufficient. Runtime unboxing also does not mean two nominal types are equal in the logic. For example, a bounded wrapper may need a proof that an operation stays in range, even when its runtime representation is just a number.

A good first step is ordinary library functions that construct an instance from explicit maps and the properties they require. An ordering can be pulled back along an injective key function with suitable laws; an equivalence gives a more general transport mechanism. Printing needs less evidence than equality or ordering, so the APIs should not require identical machinery for every interface.

This has direct value for domain wrappers and alternate orderings. It also establishes the semantic contracts a future `derive … via …` convenience would have to satisfy. No unchecked representation casts are needed.

**Recommendation:** library first. General user-defined deriving belongs with the metaprogramming design below. Existing automatic `DecEq`, `Ord`, `Show`, `Finite` and extensionality support should remain the default path where it already works.

### 7.4 Separate construction privacy from reduction opacity

OCaml supports abstract types and read-only private types: clients may be allowed to inspect a value while construction stays behind approved functions. Rust similarly makes visibility part of a type's public construction API. The OCaml distinction is particularly useful for verified programs. [OCaml modules and private types](https://ocaml.org/docs/modules).

Stitchwort currently has no `private`, and `opaque def` controls unfolding rather than whether clients can construct data. File-private helpers are already tracked in SW-150. A stronger abstract type boundary is a separate problem.

The concrete motivation is the public `Boxes` record in [2025 Day 8](../../aoc/src/Aoc/Year2025/Day08/Day08.sw): its meaningful relationship between points and pairs is established by a smart constructor and documented, but a client can construct another record. Possible designs are a proof field enforcing the invariant, hidden construction, or a public abstract representation with explicit observation functions and laws. The right choice depends on whether arbitrary valid values should be constructible and whether clients need structural inspection.

**Recommendation:** worth a separate design. Specify what public theorems may reveal, what ordinary computation can unfold, and how JS decoding preserves the construction invariant. Hiding a source constructor does not by itself validate external inputs or make definitional equality respect an abstraction boundary. Don't sell file privacy as the whole solution.

## 8. Metaprogramming that fits the language

### 8.1 Let users generate routine definitions and checked proofs

The strongest long-term opportunity is to stop requiring a Rust compiler change for every new kind of boilerplate generation.

There are several different precedents:

| System | Mechanism | Lesson for Stitchwort |
|---|---|---|
| Lean | Hygienic syntax macros, elaborators and proof-producing metaprograms | Syntax transformation and type-directed elaboration need different APIs |
| Idris 2 | `Elab` scripts can inspect definitions, check terms and declare definitions | A library can participate in elaboration |
| Agda | Reflected terms and a `TC` interface; macros fill an expected hole | Goal-directed generation can look like a term |
| Scala 3 | `Mirror` information supports user-defined derivation | Start with datatype structure rather than expose every compiler internal |
| Swift | Explicit macro roles and inspectable generated code | Make the kind and origin of generated declarations clear |
| Rust and Serde | Derive generation removes widespread serialization boilerplate | A small number of practical derivations can justify the machinery |

Sources: [Lean macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/), [Idris 2 reflection API](https://idris-lang.org/Idris2/base/docs/Language.Reflection.html), [Agda reflection](https://agda.readthedocs.io/en/latest/language/reflection.html), [Scala derivation](https://docs.scala-lang.org/scala3/reference/contextual/derivation.html), [Swift macro guide source](https://raw.githubusercontent.com/swiftlang/swift-book/main/TSPL.docc/LanguageGuide/Macros.md), [Serde derive](https://serde.rs/derive.html).

Potential uses include serializers and parsers with round-trip theorems, lawful traversals over an AST, domain-specific generators, finite tables, and specialized proof procedures returning ordinary proofs. Each is a candidate workload, not a claim that general derivation is straightforward for indexed or dependent types.

A staged route would be:

1. **Inspect existing generation.** Show a generated theorem's signature, definition and origin; navigate to the input that caused it. Source mappings and diagnostics are useful now.
2. **Generate ordinary source externally.** A tool consumes explicit project data or a stable datatype description and emits reviewable `.sw` files. The existing compiler checks everything. This tests demand without a language extension.
3. **Expose a restricted derivation API.** Offer datatype descriptions, fresh identifiers, diagnostics, and checked declaration submission. Start with ordinary nondependent products and sums.
4. **Consider goal-directed proof procedures.** A library procedure receives a restricted representation of a goal and returns a proof or a structured failure. The existing kernel checks the proof. No separate tactic script syntax is required.
5. **Only then consider general syntax extension.** Add it if the previous workloads still need it, with hygiene and scoped imports from the start.

An external generator can have ordinary tool effects; its output is explicit source. In-compiler execution needs a much tighter contract. Build-time filesystem/network access must not become invisible inputs to checking or caches. Generated definitions must pass positivity, universes, termination and erasure checks just like handwritten ones. A declaration generator must not create an unchecked escape hatch under another name.

**Recommendation:** high potential, large commitment. Pick one workload and compare external generation, a small compiler-supported derive, and a general API. A schema codec with actual laws or an AST traversal is a better demonstration than a macro that saves three tokens.

### 8.2 Compile-time data processing and schema generation

Zig makes compile-time evaluation explicit and provides a quota for its work. F# type providers offer typed access to external schemas and other data sources, including on-demand provided members. [Zig comptime and branch quotas](https://ziglang.org/documentation/master/index.html#@setEvalBranchQuota), [F# type providers](https://learn.microsoft.com/en-us/dotnet/fsharp/tutorials/type-providers/).

Stitchwort already computes pure total functions while checking types, and types themselves are values. A `comptime` keyword is not needed merely to reproduce that capability. The useful additions would be explicit, bounded generation of static data or code, with a clear diagnostic when the budget is exceeded.

For external schemas, steal the user benefit while retaining explicit inputs: generate types and decoders from a checked-in schema snapshot, record the generator and input hashes, and review the generated API. Don't query a live database or URL as an invisible consequence of opening a file in the editor.

The proof question is separate from generation. A decoder should validate representation invariants; a theorem about round trips needs a precise schema semantics and an actual proof. A provider that produces well-typed bindings has not proved the external service behaves as described.

**Recommendation:** worthwhile when interoperability work needs it. First implement as an external source generator. General compile-time staging, runtime code quotation and arbitrary type providers would be architectural bets with little current evidence of demand.

### 8.3 Hygiene and reproducibility are part of the feature

Lean's macros explicitly address both capture by introduced local binders and accidental resolution to different global names. Rust procedural macros, by contrast, have an execution model that permits broad host access and can hang compilation. These are useful design contrasts, not reasons to copy either system wholesale. [Lean macro hygiene](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/), [Rust procedural macros](https://doc.rust-lang.org/reference/procedural-macros.html).

Any Stitchwort design should specify fresh names, declaration ownership, generated-name collisions, imported capabilities, work limits, diagnostics and all dependencies affecting output. Reflection over names and types makes an important cache distinction: renaming a definition may leave its semantic hash unchanged while changing generated documentation or a name-based encoding. A generator cache must include the metadata it actually observes, not only the semantic dependency hashes.

Kernel checking protects logical acceptance of generated code. It does not guarantee the generated program has the intended API, preserves effects or implements the intended domain specification. Inspectable expansion and examples remain necessary parts of the development experience.

## 9. Attractive features to borrow selectively or defer

| Feature | What is attractive | Position for Stitchwort |
|---|---|---|
| Haskell `do`, OCaml `let*`, F# computation expressions | Pleasant sequencing for library-defined computations | Direct-style abilities already cover the main purpose. Borrow block passing; avoid a second general sequencing system |
| Rust `?` and optional chaining | Flat success paths | `?` already means a goal; `Fail.need`, `orFail`, `map` and handlers cover much of the use case |
| Kotlin implicit receivers | Very compact DSLs | Prototype explicit builders first; extra scope resolution is a real cost |
| TypeScript `satisfies` | Check a value against a shape while retaining useful inferred information | Stitchwort has nominal records and no comparable structural subtyping. Borrow expected-type guidance and precise errors, not the operator verbatim |
| Haskell pattern synonyms | Names for repeated tree shapes | A possible small extension after demonstrating repeated patterns |
| General F# active patterns | Domain-specific matching | Certified view functions first; no arbitrary effectful functions inside patterns |
| Lean global `simp` database and `grind` | Powerful end-to-end automation | Existing studies and decisions require motivating proofs. Prefer explicit dependencies and checked output |
| Lean tactic scripts | Extensible proof control | Conflicts with the current no-tactic-language design. A proof-producing term API is a separate option |
| General syntax macros and custom operators | Compact embedded languages | Start with library APIs and restricted derivation; preserve a predictable parser and formatter |
| Idris usage annotations and linear types | Erasure control, resource protocols | Potentially valuable, but a major type-system/runtime commitment; not a convenience to smuggle into this work |
| Haskell laziness and infinite streams | Elegant producers and short-circuiting | Keep strict evaluation. Use explicit thunks and bounded/total producers; codata needs its own totality design |
| Koka local mutation and scoped resources | Direct algorithms with isolated effects | Worth separate research, especially for resource APIs; don't infer totality from a mutable surface or ordinary handler syntax |
| F# live type providers | Typed access to huge external information spaces | Snapshot-backed source generation is a better initial fit |
| Unison code database and distributed code mobility | Refactoring and remote execution tied to hashes | Borrow watches and structural tools; keep the explicit source-file decision |
| TypeScript conditional/template-literal types | Expressive type-level APIs | Ordinary functions over types already offer another route. Structural typing machinery would be a separate language direction |

The TypeScript comparison is grounded in its [4.9 `satisfies` description](https://www.typescriptlang.org/docs/handbook/release-notes/typescript-4-9.html). The linearity and codata recommendations follow Stitchwort's [design](../../DESIGN.md) and existing [inductive-type research](inductives.md); they are not findings that those features are unsuitable in all languages. Koka's [book](https://koka-lang.github.io/koka/doc/book.html) is a useful source for isolated state, but its named/scoped-handler section is currently a pointer to examples, so no detailed recommendation here rests on that section alone.

## 10. Experiments that would make the choices concrete

I would take four bounded experiments forward before committing to a broad roadmap:

1. **Type-directed edits.** Add a prototype action for a dependent case split and a constructor refinement. Compare the resulting source with the current manual workflow. Include CLI access and stale-document rejection.
2. **Block arguments.** Rewrite a small sample of handler-heavy Rogue tests and parser code on paper with explicit block arguments and rest-of-scope sugar. Review the parser rule, evaluation order and proof readability before choosing a spelling.
3. **Explain an expression.** Produce a compact inspection result for one successful implicit proof, one failed implicit proof, and one recursive call. Reuse current metadata and show source-level terms. This provides a foundation for better diagnostics and metaprogramming inspection.
4. **Function-specific reasoning principles.** Continue the existing cases/equations/induction design against three real proofs. Show the generated signatures and the proofs that consume them, including a negative example the generator must refuse.

The next library pilots would be a certified view and a valid-state generator for Rogue. Neither needs a language extension. Their success would provide better evidence for future reflection and derivation than adding a general macro mechanism first.

Success should mean fewer manual steps, understandable resulting code, useful failures and acceptable latency. Track those directly: edits required to finish a task, accepted suggestions, remaining proof obligations, checking time and effect-order regressions. Token count alone rewards terse code even when the hidden obligations become harder to understand.

## 11. Scope and evidence

This is a selective feature survey, not an exhaustive language comparison or a benchmark of the other compilers. Primary documentation and implementation sources were consulted for Lean, Idris 2, Agda, Rocq Equations, Isabelle, Haskell/GHC, OCaml, F#, Koka, Unison, Rust, Swift, Scala, Kotlin, TypeScript and Python's Hypothesis. Language/library behavior is cited at the relevant discussion; the proposed adaptations and rankings are my inferences.

For Stitchwort, the baseline was the current syntax and guide, CLI/LSP code, derivation and list-attachment code, selected AoC/Rogue examples, existing proposals, research registers and relevant board statuses. No language implementation, board tickets or existing proposal decisions were changed. No full test run was needed for this report, and the proposed syntax was not implemented or presented as a working prototype.

Related local reports: [AoC corpus review](aoc-corpus-review.md), [documentation research](documentation.md), [agentic proving](agentic-proving.md), [elaboration](elaboration.md), [proof automation](proof-automation.md), [inductive types and recursion](inductives.md), and [the documentation proposal now following the earlier research](../proposals/documentation.md).

# Proposal: `Partial`

**Status:** draft 2, 15 October 2026. Open: nothing here is decided or implemented. Draft 1 was split out of [`abilities.md`](abilities.md) after review found its design unsound; this draft keeps that history (§2), adds a survey of how other systems handle non-termination (§5), compares five designs (§6), and recommends one (§7). Until this is settled there is no `Partial`, and every definition must pass the termination checker.

This note is meant to be read without knowing the codebase: §1 describes the parts of Stitchwort it touches, checked against the source at commit `0fbec9d`. Claims about other systems cite their sources ([Sources](#sources)). Anything not verified is marked **unverified**; [What I couldn't verify](#what-i-couldnt-verify) lists the gaps.

## Contents

0. [Summary](#0-summary)
1. [Background: Stitchwort today](#1-background-stitchwort-today)
2. [Why draft 1 didn't work, and the general lesson](#2-why-draft-1-didnt-work-and-the-general-lesson)
3. [Goals and non-goals](#3-goals-and-non-goals)
4. [Motivating programs](#4-motivating-programs)
5. [How other systems do it](#5-how-other-systems-do-it)
6. [Options](#6-options)
7. [Recommendation: descriptions, tied by an opaque `Delay`](#7-recommendation-descriptions-tied-by-an-opaque-delay)
8. [What can go wrong](#8-what-can-go-wrong)
9. [Staging](#9-staging)
10. [Open questions for the reviewer](#10-open-questions-for-the-reviewer)
11. [What I couldn't verify](#what-i-couldnt-verify)
12. [Sources](#sources)

## 0. Summary

**In plain words.** A function that might run forever will say `{Partial}` in its type, and so will everything that calls it. Inside the compiler, a partial function doesn't call itself. Each place where it would recurse becomes a *request* ("please run me again on this argument"), so the function's body is an ordinary, finite, total piece of code that the existing checker already understands. Requests are tied together into an endless loop only by one new built-in type, `Delay`, and the type checker can't look inside it. Only `stitchwort run` (and, later, the playground and JavaScript) actually runs a `Delay`, one step at a time. Total code can never wait for a `Delay` to finish, so a partial function can't hide inside a total one. Later, total code may be allowed to look at a `Delay` for a bounded number of steps ("fuel"), always getting `Maybe` an answer.

**For the reviewer.** The recommendation (§7) combines McBride's `General` [C4] with Capretta's delay monad [C1]:
- A partial definition is elaborated to a *description*: a total function `(x : A) -> Delay (Rec A B + Σ) (B x)` whose recursive calls are operations of a private recursion signature `Rec A B`.
- A new opaque kernel type former `Delay op res a`, with constants `now`, `lift`, `bindD`, `mapSig` and `pfix`, ties the knot: `pfix` turns a description into the recursive function.
- In stage 1, `Delay` has **no eliminator and no computation rules in the kernel**. Consistency then holds in any model where `Delay op res a` is inhabited. Totality of `Partial`-free code is unaffected, since it can't observe a `Delay`.
- The runtime gives `Delay` its meaning by a total `step : Delay op res a -> Comp op res (Next a (Delay op res a))`. Between two `Later`s a computation is a finite `Comp` segment, and every unfolding of `pfix` inserts one `Later`.
- Stage 2 exposes `step` (and so fuel-bounded observation) to total code. That's safe only because a description can't hold its own knot: it can *request* a recursive call but never step one. §8.3 gives the counterexample that rules out the simpler `pfix : ((A -> Delay B) -> A -> Delay B) -> …`. Handlers whose residual row contains `Partial` are excluded in stages 1–2. A productive `interp`-style handler, after Interaction Trees [I1], is a stage 3 candidate.

## 1. Background: Stitchwort today

Stitchwort is a small, strict, pure, dependently typed language written in Rust, built for fun and to explore ideas. A large elaborator (`crates/elab`) turns surface syntax into a small core, and a separate kernel (`crates/core`) re-checks every declaration. Only the kernel is trusted. Programs extract to JavaScript (`crates/js`), and a playground runs the compiler as WebAssembly (`crates/web`).

**The guarantee the user cares about most:** a function whose type doesn't mention `Partial` really terminates, including everything it calls, with no escape hatch. Lean is the motivating counterexample: its `partial def` is invisible in types, so ordinary code can call one and hang (§5.4). DESIGN.md §2 states it as principle 1: "No `Partial`, no divergence… No annotation, attribute or handler can quietly remove it." Principle 2: "Checking never runs effects."

**The kernel** (from [`mutual-recursion.md`](mutual-recursion.md) §1, which describes it in more detail):
- data types with parameters but no indices, strict positivity, numbered universes without polymorphism or cumulativity, and an impredicative `Prop`;
- definitions are case trees, checked by a structural termination checker. The checker accepts if one parameter position decreases in every recursive call. Size-change termination is being added for mutual recursion;
- declarations are admitted one at a time, and each must be *final* before anything may use it ([`kernel-admission.md`](kernel-admission.md)).

**Abilities are data** ([`abilities.md`](abilities.md), implemented). An effectful function type `A -> {E | e} B` is translated to a function into the prelude's inductive tree type (`crates/elab/src/prelude.sw`, line 584):

```
type Comp (op : Type) (res : op -> Type) (a : Type) : Type =
  | Done (value : a)
  | Call (o : op) (rest : res o -> Comp op res a)
```

- Rows are signatures combined with `Plus` (`L`/`R`), with explicit `SigMap` mappings between them.
- A row variable `e : Sig` (with `Sig : Type 1`) stands for the rest of a row.
- A handler is a fold over `Comp`, checked by the ordinary termination rule. Applying the `rest` field of a matched `Call` counts as structurally smaller.
- Every `Comp` is a well-founded tree, so every handler terminates. Handlers may resume any number of times (`allResults` resumes twice).
- There's no special effect machinery in the kernel.

**`IO`, `main` and the runner** ([`text-and-io.md`](text-and-io.md), implemented):
- `IO` is an ordinary prelude ability with `print : Text -> {IO} ()` and `readLine : () -> {IO} (Maybe Text)`. `Nothing` means end of input.
- `simulate : List Text -> (() -> {IO | e} a) -> {e} Pair (List Text) a` is an ordinary handler that runs a program against scripted input.
- `stitchwort run` checks `main : () -> {IO} ()`, then interprets the `Comp` tree that `main ()` evaluates to (`crates/driver/src/run.rs`). It evaluates to the next `Done` or `Call`, performs the operation, applies `rest` to the reply, and loops. Each step between operations gets its own resource budget, so a long interactive run doesn't run out just by running long.
- The playground's Run button uses the same runner, with scripted input, a 256 KB output cap, a 15-second timeout and a Stop button.

**Today interactive programs need fuel.** Every `Comp` is finite, so a total `main` performs finitely many operations. `examples/accept/adder.sw` adds numbers "until an empty line or end of input", but its loop is `addLines : Nat -> Nat -> {IO} Nat`, structurally recursive on a budget, and `main` calls `addLines 1000 0`. Its 1001st number is silently ignored. A REPL or a server can't be written at all.

**JavaScript.** Exports must be pure (DESIGN.md §12). Generated code turns a function's self tail calls into loops; other recursion uses the JS stack and fails cleanly with `StitchwortResourceError`. The kernel's own evaluator is a stack-safe abstract machine ([`stack-safe-evaluation.md`](stack-safe-evaluation.md)).

## 2. Why draft 1 didn't work, and the general lesson

### 2.1 Draft 1

Draft 1 represented a partial computation as a `Comp` tree that may be infinite, built by guarded recursion:

```
spin n = Call later (\_ -> spin n)
```

But `Comp` is *inductive*: its fold (any structurally recursive function over it) assumes every path through the tree ends. With an infinite tree available, an ordinary function proves anything:

```
drain : Comp LaterOp LaterRes a -> a
drain (Done x)          = x
drain (Call Later rest) = drain (rest ())

forever : () -> Comp LaterOp LaterRes Void
forever () = Call Later (\_ -> forever ())

contradiction : Void
contradiction = drain (forever ())
```

Two things don't help:
- **Not unfolding `forever` during type checking.** The kernel would still have admitted an inhabitant that its own eliminator proves can't exist.
- **"Users may not handle `Partial`".** `drain` is an ordinary function over an ordinary type.

This is a must-reject test (`examples/soundness/infinite-computation.sw`), and the termination checker refuses `forever`.

### 2.2 The general lesson

Draft 1's failure is an instance of two facts. Together they shape every option in §6.

**Fact 1: a type that may hold an endless computation can't have a structural recursion principle over the endless part.**
- Turner [T1] keeps "finite data and infinite codata" separate for this reason: "Ordinary recursion is not legal over codata, because it might not terminate."
- So partial computations need a type other than `Comp`, or a part of `Comp`'s structure that the termination checker never treats as smaller.
- Every design below either adds such a type to the kernel or avoids building endless values at all.

**Fact 2: a single, uniform `Partial` signature that carries the code to run next is Landin's knot.**
- Suppose `Partial` were an ordinary ability whose operation carries the suspended rest of the computation, say `later : (() -> {Partial | e} a) -> {Partial | e} a`. Its payload type mentions `Comp` over the very signature being declared.
- That's the `Cell` pattern the kernel already rejects by positivity (`examples/soundness/cell-operation.sw`). The rejection is right: non-positive types break consistency on their own, Partial or not.
- So inside the existing kernel a partial computation can't be *uniform* data. Either each partial function gets its own signature (McBride's `General` [C4], §6.1), or the knot is tied by something outside the inductive types (§6.2, §7).

## 3. Goals and non-goals

**Goals.**
1. **Visible in types.** A function that may not terminate has `Partial` in its row (`Nat -> {Partial} Nat`), and calling one makes the caller `Partial`. There's no `assert_total`, `TERMINATING` or `pretend-no-div`. Declaring a foreign function total remains a tracked `assume` (DESIGN.md §5 rule 6).
2. **Ordinary functions stay total.** A function whose type has no `Partial` terminates, everything it calls included: the same guarantee as today, with the same proof.
3. **Only the runtime runs partial code without a bound.** That means `stitchwort run`, the playground's Run button, and later JavaScript.
4. **The type checker never runs partial code.** It never unfolds a partial definition while comparing types.
5. **Proofs never depend on partial code.** No proof of `P` can be obtained by running something that might not finish.
6. **The motivating programs (§4) are easy to write**, without a fuel argument, and keep working with handlers and other abilities as far as is safe.
7. **A small trusted addition**, with a soundness argument a reviewer can check.

**Non-goals (for now).**
- Proving properties of partial programs beyond what fuel gives (stage 2). Bisimilarity-based reasoning [C1, C2, C3, I1] is out of scope.
- General user-defined coinductive types (streams, infinite trees). §6.2 discusses why they're a larger step.
- Distinguishing *productive* interactive loops from *silent* divergence. Agda and Idris treat `cat` as total because it does I/O between iterations [T2, D5]. Here it is `Partial`. §10, question 6, asks whether to revisit this.
- Wall-clock limits. A step bounds work, not time, and a host request may block.

## 4. Motivating programs

These are written in Stitchwort syntax as it would be with `Partial`. The surface language has no `case` expression yet, so helpers do the matching.

**1. A `main` that reads until end of input.** This is `adder.sw` without its fuel:

```
-- Adds up numbers, one per line, until an empty line or the end of input.
addLines : Nat -> {IO, Partial} Nat
addLines total = step total (readLine ()) addLines

-- As in adder.sw, but `more` may now be partial.
step : Nat -> Maybe Text -> (Nat -> {IO, Partial} Nat) -> {IO, Partial} Nat
step total Nothing  more = total
step total (Just l) more =
  if textIsEmpty l then total else stepNumber total l (textToNat (textTrim l)) more

main : () -> {IO, Partial} ()
main u =
  let total = addLines 0
  print ("The sum is " ++ natToText total)
```

`step` and `stepNumber` aren't recursive. They're total functions that mention `Partial` only because their argument `more` may be partial. `addLines` passes itself to `step` unapplied, which the termination checker refuses today. Under `Partial`, recursion isn't checked.

**2. A server loop with state.**

```
-- Answers commands until the input ends, keeping a count of each kind.
serve : Counts -> {IO, Partial} ()
serve counts = respond counts (readLine ())

respond : Counts -> Maybe Text -> {IO, Partial} ()
respond counts Nothing    = print "bye"
respond counts (Just cmd) =
  let counts' = record cmd counts      -- total
  print (report counts')                -- total
  serve counts'
```

The state is an explicit argument. With `runState` around a partial computation, it could be an ability instead. That's a handler with `Partial` in its residual row, which stages 1–2 exclude (§7.5).

**3. An interpreter for an untyped language.**

```
type Term : Type =
  | Var (index : Nat)
  | Lam (body : Term)
  | App (fun : Term) (arg : Term)

-- Call-by-value evaluation to weak head normal form, by substitution.
eval : Term -> {Partial} Term
eval (Var i)   = Var i
eval (Lam b)   = Lam b
eval (App f a) = apply (eval f) (eval a)

apply : Term -> Term -> {Partial} Term
apply (Lam b) v = eval (subst 0 v b)   -- subst is total
apply f       v = App f v

-- (\x. x x) (\x. x x) never finishes:
omega : Term
omega = App (Lam (App (Var 0) (Var 0))) (Lam (App (Var 0) (Var 0)))
```

`eval omega : {Partial} Term` is fine to *write*: building the computation is total, and only running it may not finish. `eval` and `apply` are mutually recursive, which needs the mutual-recursion work.

**4. A search that may not finish.**

```
-- The first n, counting up from start, with p n. Loops if there's none.
firstFrom : (Nat -> Bool) -> Nat -> {Partial} Nat
firstFrom p n = if p n then n else firstFrom p (n + 1)

collatzSteps : Nat -> {Partial} Nat
collatzSteps 1 = 0
collatzSteps n = 1 + collatzSteps (if even n then n / 2 else 3 * n + 1)
```

**And what must stay impossible:**

```
innocent : Nat -> Nat
innocent n = collatzSteps n + 1          -- error: calls a Partial function

sneaky : Nat -> Nat
sneaky n = runSomehow (collatzSteps n)   -- error: there's no such total function

theorem : Void
theorem = spin ()                        -- error: spin () : {Partial} Void isn't Void
```

## 5. How other systems do it

For each system: how divergence is represented, how it shows in types, what the checker or kernel may assume, how it's run, how it interacts with other effects, and known pitfalls. Quotes are from the cited primary sources. §5.12 sums up.

### 5.1 Capretta's delay monad [C1]

- **Representation.** A coinductive type: "`CoInductive Aν : Type := return : A → Aν | step : Aν → Aν`" (§3). The diverging computation is "⊲∞ = ⊲ ⊲∞": endless `step`s.
- **Equality.** Weak bisimilarity, defined coinductively, to "identify all terms of the form ⊲k ⌈a⌉ as equivalent representations of the element a". Everything is done on setoids.
- **Convergence** is inductive and divergence coinductive (Def. 3.2).
- **General recursion.** Unbounded search is "defined by corecursion (cofixpoint) on the result", emitting a `step` per candidate. The least fixed point of an operator (§6) runs "in parallel all the iterations of F", taking the first to converge, and is limited to "finitary, that is, continuous, operators".
- **Monad.** "The triple (ν, return, ∗) is a Kleisli triple on the category of setoids" (Thm. 8.2).
- **Pitfalls.**
  - Laws hold only up to bisimilarity, not the type theory's own equality.
  - Quotienting by weak bisimilarity, to get a real monad on a quotient type, is hard. Chapman, Uustalu and Veltri [C2] find that "one cannot define the multiplication" without "proposition extensionality and the (semi-classical) axiom of countable choice".
  - Altenkirch, Danielsson and Kraus [C3] avoid choice with a quotient inductive-inductive type that is "the free (pointed) ω-cpo over A". They note themselves that whether such types exist "in some computational models of type theory… has yet to be determined".

### 5.2 McBride's `General`: recursion as an effect [C4]

- **Representation.** Ordinary inductive data, no coinduction. "`data General (S : Set) (T : S → Set) (X : Set) : Set where !! : X → General S T X ; ?? : (s : S) → (T s → General S T X) → General S T X`" (§2). It's exactly Stitchwort's `Comp` with `op = S` and `res = T`. "General S T is the free monad on the functor Σ S λ s → T s → −."
- **Recursive definitions.** A recursive function is a *non-recursive* value of `PiG S T = (s : S) → General S T (T s)`, "the 'general recursive Π-type'", whose recursive calls are `call s = s ?? !!`, "a generic effect". "Each call is but a placeholder for a recursive call."
- **Running it.** "Diverse semantics can be given within a total framework by suitable monad morphisms" (abstract):
  - by fuel (§5): `petrol f n`, which "is primitive recursive, but makes no promise to deliver a value", and is "monotone in n";
  - into Capretta's delay monad (§6): `delay f = morph DelayK λ s → later (delay∞ f (f s))`, one `later` per call;
  - by a Bove–Capretta domain predicate (§8): `total f allInDom` turns a description into a genuinely total function once its domain is proved.
- **Pitfalls.**
  - "engine n is not a monad morphism unless n is zero": fuel counts aren't compositional.
  - The delay semantics' monad laws hold only "up to strong bisimilarity".
  - Composing descriptions with *different* `S`, `T` needs an explicit union of signatures. §6.1 explains why that matters for higher-order code.
- **McBride's conclusion (§9):** "There is no need to give up on the ability either to execute potentially nonterminating computations or to be trustably total… the difference is in what you can promise." He also distinguishes "a run time execution semantics which computes only with closed terms, and an evaluation semantics which the typechecker applies to open terms." That distinction is principle 2 here.

### 5.3 Interaction Trees (Coq) [I1]

- **Representation.** A coinductive type, "`CoInductive itree (E: Type → Type) (R: Type): Type := | Ret (r: R) | Tau (t: itree E R) | Vis {A: Type} (e : E A) (k : A → itree E R)`". In the library it's "the recommended negative coinductive form", defined by observation.
- **Why `Tau`.** "Representing silent steps explicitly allows ITrees to represent diverging computations without violating Coq's guardedness condition": `CoFixpoint spin : itree IO void := Tau spin`.
- **General recursion** is by combinators, not `cofix`:
  - `iter` puts a `Tau` before every loop-back (`| inl a ⇒ Tau (iter body a)`), and "makes no assumption on the shape of the loop body, a marked improvement over the intensional guardedness check required by cofix";
  - `mrec : (D ⇝ itree (D +' E)) → (D ⇝ itree E)` ties mutually recursive *requests*, McBride-style;
  - the paper calls `iter`, `loop` and `mrec` "mutually inter-derivable".
- **Effects.**
  - Handlers are `interp`, defined for any monad "provided that M supports an iteration operator, iter". Handlers are "monad morphisms in the sense that they commute (up to Tau) with ret and bind".
  - A handler maps each event to a computation. It never sees the continuation, so it can't force what comes after a `Tau`.
- **Equality.** "Equivalence up to Tau", a weak bisimulation that is "termination sensitive", defined as `nu euttF` with paco.
- **Running.** The type "extracts as a lazy datatype", with an OCaml driver `let rec run t = match observe t with | RetF r -> r | TauF t -> run t | VisF ...`. That is the shape of `crates/driver/src/run.rs`.
- **Pitfalls.**
  - "Coq's syntactic guardedness check is inherently non-compositional", which is why everything goes through `iter`.
  - Coinductive types defined by constructors break subject reduction in Coq. Abel, Pientka, Thibodeau and Setzer [C7] write that "coinduction is broken, since computation does not preserve types [Giménez 1996; Oury 2008]": dependent matching on a `cofix` value is the culprit. The Rocq manual now advises "negative coinductive types" [C8].

### 5.4 Lean 4 [L1–L4]

- **Representation.** `partial def` creates an opaque constant: "treated as opaque constants by the kernel and are neither unfolded nor reduced". "The body is discarded and only the opaque constant is retained by the kernel" [L1]. The compiler runs a separately compiled unsafe copy (read in `src/Lean/Elab/PreDefinition`; not run).
- **In types: invisible.** `partial def spin : Nat → Nat` has an ordinary function type, so any `def` may call it, and nothing propagates. This is DESIGN.md §5's motivating counterexample.
- **Soundness.** "The function's return type must be inhabited; this ensures soundness. Otherwise, a partial function could have a type such as Unit → Empty… [which] could be used to prove False even if it does not reduce." Logically, the function "is defined to be an arbitrary such function" [L1]. The *logic* stays consistent. The *programs* lose any termination guarantee.
- **`unsafe`** definitions "may only be referenced from other unsafe definitions" [L1]: an effect-like discipline, but not for partiality.
- **`partial_fixpoint`** (Lean 4.17.0, March 2025, PR #6355 by Joachim Breitner) defines "possibly non-terminating functions" that can be reasoned about "equationally" [L2]. It needs tail recursion in an inhabited type, or a monad that is an instance of `Lean.Order.MonoBind` such as `Option`. It's built on chain-complete partial orders (`Lean.Order.CCPO`, `fix_eq`) and yields "a partial correctness theorem… when the function's result is Option.some" [L1].
- **Well-founded recursion** is irreducible by default since 4.9.0 (#4061), "to prevent the expensive and often unfruitful unfolding" [L3].
- **Loops.** `repeat`/`while` go through `partial def Loop.forIn` in v4.20.0 [L4]. Current master instead has an `implemented_by` function whose erased version is `partial`. Either way, ordinary `IO` loops are partial underneath and invisible in their types.

### 5.5 Idris 2 [D1–D5]

- **Representation.** Totality is a property of *definitions*: `total`, `covering` or `partial`, with a default set by `%default`. That default is "initially set to `covering` unless the `--total` command line switch is used" [D3].
- **In types: not visible.** "Partial functions can still be used in types, but will not be evaluated further" [D1]. A `total` definition must "Not call any non-total functions" [D2], so partiality propagates through *references*, not types.
- **Checker.** "Only total functions will be evaluated during type checking" [D1]. This is the same policy as Agda's `NON_TERMINATING` and as principle 2 here.
- **Escape hatches.**
  - `assert_total x = x` and `assert_smaller`, both `%inline %unsafe` identity functions with docstrings like "Assert to the totality checker that the given expression will always terminate" [D4];
  - "In general, this function should be avoided" [D2];
  - I found no mechanism that tracks their use.
- **Interactive programs.** The *Type-Driven Development* chapter 11 code [D5] makes an infinite `IO` loop total by productivity, using `Inf`:
  - `data InfIO : Type where Do : IO a -> (a -> Inf InfIO) -> InfIO`;
  - a total, fuel-driven `run : Fuel -> InfIO -> IO ()`;
  - and one `partial` definition, `forever : Fuel; forever = More forever`, used only by `main`.

  The partiality is concentrated in a single, named, unchecked fuel supply. That's close in spirit to "only the runtime runs it unboundedly".

### 5.6 Agda [A1–A6]

- **Pragmas.**
  - `{-# TERMINATING #-}` "switches off termination checker… and marks them as terminating"; it "cannot be used in --safe mode" [A1].
  - `{-# NON_TERMINATING #-}` is "a safer version of TERMINATING which doesn't treat the affected functions as terminating": "NON_TERMINATING functions do not reduce during type checking", but "do reduce at run-time" [A1].
  - Neither shows up in types. **Unverified:** whether `NON_TERMINATING` is allowed under `--safe`. The manual page doesn't say.
- **`--safe`** disables "postulates, unsafe OPTIONS pragmas and primTrustMe" [A2].
- **Coinduction.**
  - Coinductive records with copatterns are accepted "if the option `--guardedness` is active" [A5].
  - The older `∞`/`♯`/`♭` notation is "the old way" [A5]. The standard library's `Effect.Monad.Partiality` still uses it, under `--safe --guardedness` [A6].
- **Sized types.**
  - "The option --sized-types is inconsistent with constructor-based guarded corecursion" [A2].
  - Since 2.6.2, "due to several known soundness issues with sized types (see #1201, #1946, #2820, #3026)… the `--sized-types` flag can no longer be used while `--safe` is active" [A3].
  - Issue #1201, "Check needed when ∞ < ∞ is ok for sizes", derives ⊥ and is still open [A4].
  - `Codata.Sized.Delay` is therefore not `--safe` [A6].
- **Writing interpreters.** Danielsson [C5] writes call-by-value interpreters into the partiality monad, one `later` "for every β-redex that has been reduced". But "Agda does not accept the code above", because "bind is not a constructor". The workaround is an embedded language whose constructors include `>>=`. Abel and Chapman [C6] instead use sized types so that bind is "size (observation depth) preserving".
- **Interactive programs.** `ooAgda` [T2] follows Hancock and Setzer:
  - `IO I A` is a coinductive record over an interface of commands and responses;
  - `cat` (getLine, `nothing → return unit`, otherwise putStrLn and loop) "potentially… runs infinitely long", and is accepted as total by copattern guardedness;
  - its console interface is almost exactly Stitchwort's `IO`.

### 5.7 Rocq [R1]

- **No non-terminating definitions.** There's no counterpart to `NON_TERMINATING`.
- **Unsafe flags.** Guard checking can be turned off: the `Guard Checking` flag "can break the consistency of the system, use at your own risk", and `bypass_check(guard)` does it locally.
- **Tracking.** `Print Assumptions` reports such uses ("ackermann is assumed to be guarded"). This is tracking of an *unsafe* assumption, comparable to Stitchwort's `assume`.
- **Coinduction.** `cofix` has the subject-reduction problem described in §5.3.

### 5.8 F* [F1, F2]

The closest precedent for divergence tracked in types.

- **Representation.** Divergence is an *effect* in a lattice: "PURE → DIV → STATE → ALL", plus GHOST [F1]. "PURE computations are at the very bottom… This monad forms F⋆'s logical core. It soundness depends crucially on a semantic termination check based on a well-founded order. The DIV effect is for possibly divergent code."
- **In types.** `Dv t` "describes a computation that may loop forever, but if it completes, it returns a value of type t". `Tot < Dv` in the effect order, so "Tot computations cannot rely on Dv computations" [F2].
- **Checker.** "Recursive functions that return computations in the Dv effect are not checked for termination" [F2]. Divergent code is interpreted "in a partial-correctness setting", while only PURE and GHOST are read with total correctness [F1].
- **Proofs.**
  - "One cannot even state properties of Dv computations in specifications, since even specifications must be total" [F2].
  - "Typelevel expressions are allowed to be GHOST computations", and refinements are "inhabited by expressions e : Tot t" [F1].
  - "It should be impossible to turn a e:Dv t into a term of type Tot t" [F2].
- **Running.** Extraction "to OCaml or F#" [F1]. **Unverified:** how `Dv` code specifically is extracted.
- **Pitfalls.**
  - Top-level effects: `let inconsistent : False = loop_nonpos()` is accepted with only a warning ("Top-level let bindings must be total"). Such effects "can render F*'s typechecking context inconsistent" [F2].
  - `Dv` also relaxes strict positivity and universe checks [F2]. In a lattice design the divergent fragment is a different, weaker logic, and anything that leaks from it into types is fatal.

### 5.9 Koka [K1–K3]

- **Representation.** A built-in effect constant `div` with no operations (`pub type div :: X` in `std/core/types.kk` [K3]). `total` is the empty row, and `alias pure = <div,exn>`.
- **Guarantee.** "If an expression can be typed without a div effect, then it always terminates" [K1].
- **Inference.**
  - A "simple termination checker" assigns `div` unless "each recursive call decreases the size of an inductive data type (or is productive for a co-inductive data type)". "The current analysis is quite limited and syntactically fragile" [K1].
  - Higher-order state: with Landin's knot, "reading from the heap may result in divergence", so the implementation adds `div` when a reference's type mentions its own heap [K1]. This is the `Cell` problem again.
- **Handlers.** `div` has no operations, so it can't be handled. The only way to remove it is `pretend-no-div`, documented as "_Unsafe_" [K3].
- **Rows.** `while : (pred : () -> <div|e> bool, action : () -> <div|e> ()) -> <div|e> ()` [K2]. Divergence is an ordinary row label, so row polymorphism covers it for free.

### 5.10 Unison, Dafny, Haskell and OCaml

- **Unison** [U1]. The ability documentation never mentions termination, totality or divergence. `A ->{} B` means only "requires no abilities". As far as I can tell, divergence isn't tracked (absence of evidence, not a positive statement).
- **Dafny** [Y1].
  - "Loops and compiled methods (but not functions and not ghost methods, including lemmas) can be specified to be possibly non-terminating… with decreases *."
  - "A method that contains a possibly non-terminating loop or a call to a possibly non-terminating method must itself be declared as possibly non-terminating."
  - Functions, which specifications use, must terminate. `Main` with `decreases *` "may go on forever".
  - `dafny audit` flags `decreases *`, noting it "cannot cause an unsound proof". This is propagation through calls, visible in signatures, with specifications kept total: close to the goal here, without effects polymorphism.
- **Haskell and OCaml** (from general knowledge, not cited). Divergence is pervasive and untracked: every type is inhabited by a diverging term, and `IO` loops are ordinary recursion. This is the baseline the goal rejects.

### 5.11 Guarded recursion and the later modality [G1–G6]

- **Origins.** Nakano [G1] introduced a modal logic "that enables us to handle self-referential formulae". Guarded type theories add a type former `▷A` ("later") and a fixpoint rule `(▷A → A) → A`.
- **The delay monad as a guarded type.** "L A is the unique solution to the guarded recursive type equation L A ≅ A + ▷L A", whose elements are "values 'now' or computations that 'tick'". The semantics "counts the number of unfold-fold reductions" [G5]. Time steps are visible, as in Capretta.
- **Getting out of `▷`.**
  - Guarded recursion alone can't make "finite observations on pieces of infinite data". Atkey and McBride [G2] add clock variables and clock quantification to recover genuine coinductive types.
  - Clocked Type Theory [G3] has proofs of "confluence, strong normalisation and canonicity", but "ultimately, we would like to have an implementation".
  - Guarded Cubical Agda (`--guarded`) is implemented; its manual page is "a stub" [G6].
- **Relevance here.** `▷` is exactly what stops a function from stepping its own recursive call before it has been made. §8.3's counterexample is what goes wrong without it. The recommendation gets the same protection more cheaply, by giving descriptions only *requests*, never a value of the knot.

### 5.12 Summary

| System | Divergence represented as | Visible in types | Checker may unfold it | Escape hatch | With other effects |
|---|---|---|---|---|---|
| Capretta [C1] | coinductive `Aν` | yes (`Aν`) | n/a (library) | none | n/a |
| McBride [C4] | requests in an inductive free monad | yes (`PiG`) | descriptions yes, the knot isn't in the language | none | composes as a free monad; knot tied by a chosen interpretation |
| ITrees [I1] | coinductive tree with `Tau` | yes | Coq unfolds `cofix` under `match` | none (in `itree`) | `interp`, monad morphisms that commute up to `Tau` |
| Lean 4 [L1] | opaque constant | **no** | no | `partial`, `unsafe` | invisible |
| Idris 2 [D1] | definition attribute | **no** (propagates through references) | no (only total code reduces) | `assert_total`, untracked | `IO` loops are productive codata, or `partial` |
| Agda [A1] | pragma / codata | no (pragmas); yes (codata) | no for `NON_TERMINATING` | `TERMINATING` (not `--safe`) | coinductive `IO` |
| Rocq [R1] | not supported | – | – | `bypass_check`, listed by `Print Assumptions` | ITrees |
| F* [F1] | `Div` effect | yes | no: specs are `Tot`/`GTot` | top-level effects warn only | effect lattice |
| Koka [K1] | `div` row label, inferred | yes | n/a | `pretend-no-div` (unsafe) | ordinary row polymorphism |
| Dafny [Y1] | `decreases *` on methods | in the signature | functions must terminate | none | n/a |
| Guarded TT [G3] | `▷` | yes | yes (normalising) | none | research |

Three patterns stand out:
- **Systems where partiality is invisible** (Lean, Idris, Agda pragmas) keep the *logic* consistent by refusing to unfold, but give no guarantee about *programs*.
- **Systems where it's visible** do it either with an effect (F*, Koka, Dafny) or with a type of possibly-infinite computations (Capretta, ITrees, guarded TT).
- **The "requests" idea** (McBride's `General`, ITrees' `mrec`) is the common trick that keeps the recursive knot out of user code.

## 6. Options

Each option is described by:
- its representation;
- kernel changes and trusted code;
- handlers and rows;
- `main`, `run`, `simulate` and the playground;
- JS;
- proofs;
- what goes wrong.

Ideas not chosen are worth recording too.

### 6.1 Option 1: McBride's `General` as plain data, interpreted only by the runtime

**Representation.** Each partial definition gets its own recursion signature, and its body is a total description. In Stitchwort terms, recursion is an ability private to the definition:

```
-- What the elaborator would make of `firstFrom` (§4):
type FirstFromRec : Type = | Recur (n : Nat)
FirstFromRes : FirstFromRec -> Type
FirstFromRes (Recur n) = Nat

firstFromBody : (Nat -> Bool) -> Nat -> Comp FirstFromRec FirstFromRes Nat
firstFromBody p n = if p n then Done n else Call (Recur (n + 1)) Done
```

`firstFromBody` isn't recursive. The runtime ties the knot: on `Call (Recur m) k` it runs `firstFromBody p m` and passes the result to `k`. Fuel interpretations (`petrol`) are ordinary total prelude functions.

**Kernel.** No change. Everything is existing data and existing checks. `drain` over such a tree is harmless: the tree is finite, and `drain` stops at the first `Recur`, which it can't answer. A total function that *answers* `Recur` by calling `firstFromBody` again recurses on something that isn't structurally smaller, and is refused.

**Where it breaks: composition and higher-order code.**
- **Composition.** A partial function `g` that calls `firstFrom` must either include `FirstFromRec` in its own signature, or the type must name the recursion signatures it might use. That's the call graph in the types.
- **Higher-order code.** A uniform type for "some partial function from `A` to `B`", needed for `map` over partial callbacks or a list of partial closures, must package the signature and the dispatcher existentially: `Σ (op : Type) (res : op -> Type) …`.
  - That lives in `Type 1`, because `op : Type`. Stitchwort has no universe polymorphism or cumulativity (`docs/core.md`), and `List : Type -> Type`, so a `List` of partial closures can't even be formed.
  - The row-variable alternative (an implicit row `p` of recursion signatures, unioned at call sites) avoids the universe bump but fails for genuinely unknown callbacks.
- **Handlers.** `runState` around a call to a partial function forwards the `Recur` request. The runtime then runs the callee's body *outside* `runState`, so the callee's `State` operations escape. McBride's `expand` substitutes the callee's tree *in place*, under the handler, but that unbounded expansion is exactly what total code can't do. ITrees solve this with `mrec`, which needs a type of infinite trees.

**JS, `main`, proofs.** `main`'s tree, with its signature and dispatcher, would be run by the same loop as today, extended to dispatch `Recur`. Proofs about descriptions are ordinary proofs, and a Bove–Capretta domain predicate gives totality by proof [C4, §8]. That's attractive and carries over to §7.

**Verdict.** Sound and needs no kernel change, but as *the* representation it fails goal 6 for higher-order and handled code. It remains the right *internal* form of one definition's body, and §7 keeps it for that.

### 6.2 Option 2: a separate type for possibly-infinite computations

`Comp` stays inductive. A new type, `Delay` (Capretta's name), holds possibly-endless computations. There are three variants, depending on how much of coinduction the kernel admits.

**2a. General user-defined coinduction.** Codata declarations, copatterns and a guardedness checker, as in Agda [A5], or sized types [C6]. ITrees could then be written in Stitchwort.
- **Kernel.** Large: coinductive declarations, copattern matching, a productivity checker, and a decision about eta and bisimilarity.
- **Pitfalls.** Each piece is documented elsewhere:
  - subject reduction with constructor-style coinduction [C7, C8];
  - non-compositional guardedness [I1];
  - "bind is not a constructor" [C5];
  - sized types' open inconsistencies [A3, A4];
  - weak bisimilarity's transitivity trap: naive transitivity in corecursive proofs proves `trivial : (x y : A⊥) → x ≈ y` [C5, §2].
- **Benefit.** Productive loops like `cat` become total (§3, non-goals), and streams come for free.
- **Verdict.** Too much new trusted machinery for this purpose.

**2b. One built-in type with a closed set of primitives.** No user codata. The kernel adds `Delay op res a` and a few constants (§7.2). Corecursion is possible only through those constants, so no guardedness checker is needed, provided the constants can't be used to force their own knot (§8.3). This is the recommendation.

**2c. The coalgebra encoding, with no kernel change.** A final coalgebra can be represented by an existential state and a step function:

```
type Machine (op : Type) (res : op -> Type) (a : Type) : Type 1 =
  | MkMachine (s : Type) (start : s) (next : s -> Comp op res (Next a s))
```

This is draft 1's "resumable machine" experiment, packaged.
- **Soundness.** `next` is total and finite, and the termination checker refuses any function that runs a machine to the end. Fuel-bounded running is structural on the fuel.
- **The catch.** `Machine … : Type 1`, and `bind` of two machines needs a state that contains machines, so nesting climbs universes. Without universe polymorphism it's impractical as the language's representation.
- **Use.** It *is* a cheap way to prototype the API and fuel semantics in the prelude before touching the kernel (§9, stage 0).

### 6.3 Option 3: an F*-style effect lattice in the kernel

The kernel gets a second judgment, or effect-annotated arrows `A ->Div B`:
- `Div` terms are never reduced by conversion;
- they can't appear in types;
- recursion in `Div` isn't termination-checked;
- `Tot ≤ Div`.

Consistency follows from F*'s argument: specifications are total, and `Div` is read with partial correctness [F1, F2].

- **Kernel.** Large. abilities.md chose effects as data (option B) precisely to avoid an effect judgment in the kernel, and this would add one just for `Partial`.
- **Interaction with abilities as data.** A `Div` function that performs `IO` between iterations can't return a `Comp` tree it builds strictly: it would diverge *building* the tree before performing anything. The tree's continuations would have to be `Div` arrows, giving a second, `Div`-arrowed `Comp` that total code can't fold. That's option 2b again, reached the long way round.
- **Pitfalls.** F*'s own: top-level effects in a total context [F2], and every place where a `Div` term might leak into a type or specification.
- **Verdict.** It's the right *mental model* for what the type system promises: `Partial`-free means total, and `Partial` code is never in types. As kernel machinery it duplicates what 2b gets with constants.

### 6.4 Option 4: runtime-only marking that propagates, Idris-style

`partial` is an attribute of definitions. The kernel records it, never unfolds partial definitions, and refuses partial definitions in proofs, propagating "partial" through references.

- **Kernel.** Medium: a flag per definition, a propagation rule, and an "is this a proof" check. Logical soundness also needs Lean's inhabitedness condition, because an opaque `spin : Nat -> Void` would otherwise be a proof of `Void` [L1].
- **Visibility.** None. `Nat -> Nat` might be partial.
  - Propagation through references is coarse. `mk : Nat -> (() -> Nat)`, returning a partial closure, is itself marked partial even though calling it terminates.
  - Higher-order code can't say "total if my argument is".
- **Verdict.** Fails goal 1. Listed because it's what Idris, Lean and Agda pragmas do.

### 6.5 Option 5: fuel only, possibly driven by the runtime

**5a. Explicit fuel, as today.** No change.
- Every unbounded program carries an arbitrary bound (`addLines 1000`), and silently stops when it runs out.
- `withFuel` can't be written generically, because there's no partial representation to run.

**5b. The runtime drives a total step function.** `main` is replaced, or joined, by a machine, `init : s` and `stepMain : s -> {IO} (Next () s)`. The runner calls `stepMain` until it returns `Now`. text-and-io.md already notes that "a host can also drive repeated calls to a total step function without claiming that its own driver is total". This is Idris' `Fuel`/`forever` pattern [D5], with `forever` moved into the runtime.
- **Kernel.** No change.
- **What it covers.** The `main` and server programs in §4 (1 and 2), with the loop written as a state machine. Interpreters and searches need their recursion turned into an explicit stack by hand.
- **Verdict.** A useful stopgap for `main` only. It doesn't make `Partial` a type, so it fails goal 1 for library code, but it could ship in days if the main proposal stalls.

### 6.6 Comparison

| | 1: `General` as data | 2a: user codata | **2b: built-in `Delay`** | 2c: existential machine | 3: effect lattice | 4: Idris-style | 5b: runtime-driven step |
|---|---|---|---|---|---|---|---|
| `Partial` visible in types | yes (with signatures) | yes | **yes** | yes | yes | no | n/a (only `main`) |
| Kernel change | none | large | **small: 1 type former, 5 constants, no rules (stage 1)** | none | large | medium | none |
| Higher-order and stored closures | universe bump | yes | **yes** | universe bump | yes | yes | n/a |
| Handlers with `Partial` in the residual row | broken semantics | yes (with productive handlers) | **excluded until stage 3** | excluded | yes | n/a | n/a |
| Fuel-bounded observation | yes | yes | **stage 2** | yes | no | no | no |
| Checker never runs partial code | yes | no (unfolds codata) | **yes** | yes | yes | yes | yes |
| Main risk | ergonomics | soundness of new machinery | **the knot argument (§8.3)** | universes | size | invisible | covers only `main` |

## 7. Recommendation: descriptions, tied by an opaque `Delay`

Option 1's descriptions combined with option 2b's built-in type. McBride's `delay` interpretation [C4, §6] becomes the one new kernel constant.

### 7.1 Types

```
-- The result of one step: finished, or a `Later` with the rest.
type Next (a : Type) (d : Type) : Type =
  | Now   (value : a)
  | Later (rest : d)

-- One definition's recursion signature: a request to recurse on `x`,
-- answered with a `B x`.
type Rec (A : Type) : Type =
  | Recur (x : A)

RecRes : [A : Type] -> (B : A -> Type) -> Rec A -> Type
RecRes B (Recur x) = B x
```

These are ordinary prelude data types.

### 7.2 The kernel's additions (stage 1)

One opaque type former and five constants, registered like the existing trusted natives, which must be final ([`kernel-admission.md`](kernel-admission.md)):

```
Delay  : (op : Type) -> (res : op -> Type) -> Type -> Type

now    : a -> Delay op res a
lift   : Comp op res a -> Delay op res a
bindD  : Delay op res a -> (a -> Delay op res b) -> Delay op res b
mapSig : SigMap op1 res1 op2 res2 -> Delay op1 res1 a -> Delay op2 res2 a
pfix   : [A : Type] -> [B : A -> Type] ->
         ((x : A) -> Delay (Plus (Rec A) op) (PlusRes (RecRes B) res) (B x)) ->
         (x : A) -> Delay op res (B x)
```

Implicit arguments are elided where obvious. `Delay op res a` lives in the same universe as `Comp op res a`.

**In stage 1 the kernel gives these constants no computation rules.** An application of a constant is a neutral term. Conversion compares neutral terms structurally and never unfolds anything.

There's no `case` on `Delay`, because it isn't a data type. And there's no eliminator into any other type.

Two kernel checks change:
- **Positivity.** A data type whose field mentions the type being declared inside `Delay`'s arguments is refused, as nested occurrences such as `List D` already are.
- **Termination.** No change. `pfix`'s argument is an ordinary non-recursive lambda, so a partial definition is no longer a recursive definition at all.

### 7.3 Elaboration

**A function type whose row contains `Partial`.** `A -> {Partial | ρ} B` translates to `A -> Delay op_ρ res_ρ B`, where `ρ` is the rest of the row. Without `Partial`, the translation is `A -> Comp op_ρ res_ρ B`, as today. So `Partial` isn't a signature label. It's a *mode* that selects `Delay` instead of `Comp`.

**A definition whose type has `Partial` and which refers to itself** (or a group of them, after the mutual-recursion work) is elaborated in two parts:
1. Its body is translated with each self-call `f e` replaced by the operation `recur e` of a private ability `Rec A`. The result is a description over `Plus (Rec A) op_ρ`.
2. The definition becomes `f = pfix body`.

Using the example from §4:

```
-- Source
firstFrom : (Nat -> Bool) -> Nat -> {Partial} Nat
firstFrom p n = if p n then n else firstFrom p (n + 1)

-- Core (sketch)
firstFrom p = pfix (\n -> if p n then now n else recur (n + 1))
  where recur y = lift (Call (L (Recur y)) (\r -> Done r))
```

For a group, `A` is a sum over the members, and `B` is computed from the member index. That's ordinary data, and it matches ITrees' `mrec`.

**Calling a partial function** from partial code is `bindD`, and calling one from total code is a type error: goal 1. Inside a description, calls to *other* partial functions are embedded with `mapSig` along `sigRight`.

**Subsumption.** Wherever a `{Partial | ρ}` computation is expected, a `{ρ}` one can be used. The elaborator inserts `lift`, which is cheap: one constructor around a finite tree.

**Rows.**
- Row variables range over `Partial`-free rows.
- A function polymorphic in its callback's effects, `map : (a -> {e} b) -> List a -> {e} List b`, can't be given a partial callback. A library would provide `mapP : (a -> {Partial | e} b) -> …`. Total callbacks fit it through subsumption.
- Being polymorphic in partiality itself, as in Koka, would need a type-level switch between `Comp` and `Delay`. See §10, question 3.

**Handlers.**
- A `handle` whose *clauses* call partial code is fine: its carrier is a `Delay`, and the fold is over a finite `Comp`.
- A `handle` whose *handled computation* is partial, meaning `Partial` is in the handler's residual row, is refused in stages 1 and 2. So is `Partial` instantiating a handler's row variable. That's DESIGN.md's rule 4 ("only the runtime handles `Partial`"), made precise.

### 7.4 What the runtime does

The runtime gives `Delay` its meaning by one total function, `step`. Stage 1 doesn't put `step` in the kernel; it's the specification the evaluator's run mode and the JS runtime implement.

```
step : Delay op res a -> Comp op res (Next a (Delay op res a))

step (now x)        = Done (Now x)
step (lift c)       = mapLeaves Now c                      -- finite: c is a Comp
step (bindD d k)    = bindSeg (step d) k
    -- bindSeg: Now x ↦ step (k x);  Later d' ↦ Done (Later (bindD d' k))
step (mapSig m d)   = translate m (mapLater (mapSig m) (step d))
step (pfix f x)     = Done (Later (tie f (f x)))           -- one Later per unfolding
step (tie f d)      = tieSeg f (step d)
    -- tieSeg, over the finite segment:
    --   Done (Now v)           ↦ Done (Now v)
    --   Done (Later d')        ↦ Done (Later (tie f d'))
    --   Call (R o) k           ↦ Call o (\r -> tieSeg f (k r))
    --   Call (L (Recur y)) k   ↦ Done (Later (bindD (pfix f y) (\r -> tie f (resume (k r)))))
```

- `tie` is an internal form of the runtime, not a kernel constant.
- `resume` turns the rest of a segment back into a `Delay`.
- `mapLeaves`, `bindSeg`, `mapLater` and `tieSeg` recurse structurally over a finite `Comp`.

**The invariant.** Each `step` does a finite amount of work and returns a finite segment. Every `Later` comes from an unfolding of `pfix`, either directly or through a request. Operations between two `Later`s form a well-founded `Comp`, as in draft 1's sketch ("each suspension is a well-founded `Comp` segment").

**The runner** (`crates/driver/src/run.rs`) changes little:
- `main : () -> {IO, Partial} ()` is accepted as well as `() -> {IO} ()`, which is lifted.
- The loop evaluates `step` on the current `Delay` and walks the segment as it walks a `Comp` today: perform each `Call`, apply the continuation.
- At `Later d'` it continues with `d'`. At `Now ()` it stops.
- Each step is one budgeted operation, as now. So a single step that does too much is still `E-RESOURCE`, but the number of steps is unbounded.

**What one unit of fuel is**, answering draft 1's questions:
- **What produces a step?** One unfolding of a partial definition, which is one recursive call.
- **Do operations cost fuel?** No: segments are finite.
- **Do transformations need to preserve the count?** Yes, because `Later`s are part of the value. That's only observable from stage 2 on.
- **Is fuel per path or shared?** Per path under multi-shot handlers. No multi-shot handler can see a `Delay` before stage 3 anyway.
- **Is a step a unit of time?** No.

**The playground** uses the same runner. It already has the 15-second timeout and Stop that an unbounded program needs.

**`simulate`** can't run a partial `main` in stage 1, since that would be a handler with `Partial` in its residual row. Tests of partial programs are instead driver-level scripted runs with a step budget. Exceeding the budget is *inconclusive*, never pass or fail, like a test that runs out of resources (DESIGN.md §7). Stage 2 adds `simulateFor`, a fuel-bounded version in the language.

### 7.5 JavaScript

Exports stay pure (DESIGN.md §12), so in stage 1 no generated JS needs `Delay`.

When JS needs it (running `main` in the browser without the evaluator, or exporting partial functions):
- **The runtime implements `step` natively.** A `Delay` is a small object (`now`, `lift`, `bindD`, `mapSig`, `pfix`, `tie`).
- **Stack safety.** Left-nested `bindD`s are re-associated as Bjarnason's trampoline does ("It's critical to resolve this case in such a way that remains productive without introducing new stack frames. The trick is to re-associate the expression to the right" [T3]). So `step` runs in constant JS stack, whatever the nesting of a partial interpreter's calls.
- **A partial export returns a stepper** instead of a value: `{ run(maxSteps): { done: true, value } | { done: false } }`. The host chooses the budget and can yield to the event loop between calls. A blocking `runForever()` convenience is a host decision. (§10, question 7.)
- **Top-level partial values** are emitted as unevaluated `Delay` objects, so nothing partial runs when a module loads. F*'s top-level-effects pitfall [F2] can't arise, because a `{Partial} Void` is a value of type `Delay … Void`, not a `Void`.

### 7.6 Proofs about partial programs

- **Stage 1.** Nothing about a `Delay` can be proved beyond syntactic identities. But a *description* is an ordinary total function, so its properties are ordinary theorems. For example: "`collatzBody 1 = now 0`", or "every request `collatzBody n` makes is on a smaller argument". From the latter a total version follows, as with McBride's Bove–Capretta construction [C4, §8]. That's the honest route from "partial" to "total": prove it terminates, then use the total function.
- **Stage 2.** With `step` exposed, `runFor` is definable (§9), and with it:
  - **convergence:** `∃ n. runFor n d = Done (Just v)`, Capretta's inductive convergence [C1];
  - **partial correctness:** `∀ n v. runFor n d = Done (Just v) -> P v`, F*'s and `partial_fixpoint`'s notion [F2, L2].

  Bisimilarity isn't needed for either.

### 7.7 Why it's sound: the argument

**Stage 1: consistency and totality of `Partial`-free code.**
1. *Consistency.* The kernel only gains an opaque type former and constants with no computation rules. Any model of the existing theory extends by interpreting `Delay op res a` as any inhabited set and the constants as any functions of the right types (`Delay op res a := 1` works). Conversion is unchanged on old terms, and new terms are neutral. So no new closed proof of `Void` exists. Unlike Lean's `partial` [L1], no inhabitedness side condition is needed: `Delay … Void` is a different type from `Void`, and nothing maps one to the other.
2. *Totality.* A `Partial`-free closed term's evaluation is the old evaluation. The only new values it can hold are `Delay` values, and no total function inspects them: there's no `case`, no eliminator, and no reduction rule.

   So the existing argument applies, treating `Delay` values as opaque constants. A total function receiving a `{Partial}` callback can only build bigger `Delay`s with it.
3. *Draft 1's `drain`* has no counterpart. There's nothing to recurse on.

**Stage 2: when total code may `step`.** This needs a real argument, and the reviewer is asked to check it (§10, question 1). The outline:

1. *A model.*
   - Interpret `Delay op res a` as the final coalgebra of `X ↦ Comp op res (Next a X)`: possibly infinite sequences of finite segments.
   - It exists because the functor is polynomial: `Comp` is the free monad over a container, and containers compose, so it has an M-type. Ahrens, Capriotti and Spadotti construct M-types type-theoretically [M1]; set-theoretically it's standard. **This hasn't been checked for this exact functor.**
   - `step` is the coalgebra's destructor, and `now`, `lift`, `bindD` and `mapSig` are the obvious maps.
2. *`pfix` has a meaning without any continuity condition.*
   - Because a description gets *requests*, not the function being defined, `pfix f` can be defined by coiteration. Take a coalgebra whose state is a stack of pending continuations and whose structure map steps the top description. That uses only `f`, `step` on already-defined values, and finite segment walks.
   - Compare the rejected form `pfix : ((A -> Delay B) -> A -> Delay B) -> …`. There, `f` receives the function being defined, and an arbitrary set-theoretic `f` need not have a fixed point. `f g x = if g x = later (now 0) then now 1 else now 0` has none: a solution would need `g x = later (f g x)`, and both cases contradict themselves. So the rejected form needs a model where all functions are continuous or non-expansive, such as the topos of trees behind guarded type theory [G5]. The request form doesn't.
3. *Each `step` terminates.*
   - Every user function that `step` invokes is the description `f`, a continuation `k` of `bindD`, or a mapping inside `mapSig`. Each of these receives only values built *before* the `step`, and never a `Delay` that contains the `pfix` application being unfolded.
   - A description can't name its own knot: it has `recur`, not `f`. Top-level self-reference is refused by the termination checker. Self-application would need a non-positive type, refused by positivity.
   - So any `step` that total code performs inside such a function is on a strictly earlier `Delay`. Induction on construction order should make this precise. **That induction is an outline, not a proof.** §8.3 shows exactly what fails without the request form.
4. *Totality of code that uses `step`.* `drain`-like functions recurse on `step`'s result. That isn't structurally smaller, so they're refused. The only total way through an unbounded number of `Later`s is structural recursion on something else, such as fuel.

**Not covered by the argument:** stage 3 handlers (§8.4), and `step` in *conversion* (§10, question 2).

### 7.8 Trusted code

All of these are estimates.

| Where | What | Size |
|---|---|---|
| Kernel (`crates/core`) | `Delay` type former and five constant signatures; neutral treatment; positivity treats `Delay`'s arguments as non-positive positions | ~100–200 lines |
| Evaluator, run mode | `step` as in §7.4 (and `tie`); stack-safe, since the machine already keeps frames on the heap | ~150 lines |
| Runner | accept `{IO, Partial}`; loop on `step` | ~40 lines |
| Stage 2: kernel | `step` becomes a constant with computation rules (§7.4) in run-mode evaluation | ~100 lines |
| Later: JS runtime | native `step` with re-association | ~150 lines of JS |

The elaborator's work is untrusted: the `Rec` translation, mode selection, `lift` insertion, and the handler restriction's error messages. Getting it wrong can produce rejected or wrong-but-total programs, never an unsound one. The exceptions are the type restriction on handlers and the `Partial`-in-type check, and the kernel enforces both: a handler fold over `Delay` has nothing to fold, and a total type is a `Comp` type.

## 8. What can go wrong

Each pitfall is paired with what prevents it. Each should become a must-reject test in `examples/soundness/`.

### 8.1 `drain`, generalised

Any total function that recurses through the endless part of a computation proves `Void`.
- **Stage 1.** There's nothing to recurse on.
- **Stage 2.** `drainD d = … drainD d' …` with `d'` from `step d` is refused: `d'` isn't a structural descendant.
- **Test.** `drainD` written with `step` (stage 2), and a `case` on a `Delay` built by hand (kernel: not a data type).

### 8.2 A handler that "acknowledges every step"

DESIGN.md §5 rule 4 exists for this case. A handler for `Partial` that answered each step and resumed would turn an endless computation into a "total" one.
- Here, `Partial` isn't an ability with operations, and there's nothing to handle. Koka's `div` has no operations for the same reason [K3].
- The only total observers are fuel-bounded and return `Maybe`.
- **Test.** A handler naming `Partial`; a `handle` with `Partial` in its residual row (stages 1–2); `Partial` instantiating a handler's row variable.

### 8.3 Forcing the knot

This is the reason for the request form. Suppose `pfix` gave the description the function being defined:

```
pfixBad : ((A -> Delay B) -> A -> Delay B) -> A -> Delay B
step (pfixBad f x) = Done (Later (f (pfixBad f) x))
```

In stage 2, total code can `step`. Then a description can step its own recursive call past the `Later`:

```
f self x = stepTwice (self x)   -- stepTwice: step, take the Later's rest, step it
```

- `step (pfixBad f x)` gives `Later (f (pfixBad f) x)`.
- Stepping that rest evaluates `f (pfixBad f) x`, which steps `pfixBad f x`: one `Later`.
- It then steps that `Later`'s rest, which evaluates `f (pfixBad f) x` again, and so on.

So a single `step`, a total function, never returns. Fuel doesn't help, because every invocation of `f` gets fresh fuel.

The same shape appears in Coq as the guard condition's ban on eliminating corecursive calls [I1, footnote 3], and in guarded type theory as `▷`, which makes `self x` unavailable "now" [G1, G5].
- **The request form prevents it.** A description has `recur`, which produces a request that only `tie`, inside the runtime, answers. `step` on a description returns `Call (L (Recur y)) k`, a finite answer, and never runs the callee.
- **Test.** In the kernel, a hand-built `pfix` whose description mentions `pfix` of itself: that needs a recursive definition, so the termination checker refuses it. In the elaborator, a partial definition never translates a self-call into anything but `recur`.

### 8.4 Deep handlers on partial computations (stage 3)

The same knot appears if a generic handler on `Delay`, say `foldD`, gives clauses a continuation that leads, past a `Later`, back into `foldD` on the rest. A clause that steps its continuation's result runs the next clause, which steps again: unbounded, inside one `step`.
- ITrees avoid it because `interp`'s handlers "map each event to a computation" and never see the continuation, and `iter` inserts a `Tau` [I1].
- So stage 3, if it comes, should offer `interp`-style handlers: monad morphisms from operations to `Delay`, run into a state-passing or `Maybe`-passing carrier. They should not offer arbitrary deep handlers with continuation access. Multi-shot handlers (`allResults`) on partial computations stay fuel-only.
- **Test** (stage 3). A clause that steps its continuation's result is refused or inexpressible.

### 8.5 Equality and conversion on partial values

- **Stage 1.** Conversion never unfolds `pfix`, so the checker can't loop on partial code. `rfl : collatzSteps 1 = now 0` fails. It's true at runtime, but the checker never runs partial code.
- **Equality.** Syntactically equal `Delay` terms are equal, which every model respects. There's **no eta rule** for `Delay` (no `d ≡ roll (step d)`): comparing two `Delay`s by stepping both is bisimilarity, which is undecidable and would make conversion unfold forever.
- **If stage 2 lets conversion compute `step`** on concrete terms, each `step` is finite (§7.7), and nothing steps a `Later`'s payload without an explicit `step` in the term. **Not proven:** that conversion then still terminates on open terms.
- **Tests.**
  - `rfl : collatzSteps 1 = now 0` is refused in stage 1.
  - `Vec Nat (collatzSteps 5)` is a type error (`Delay` isn't `Nat`).
  - A proof of `Void` from `spin () : {Partial} Void` is refused.

### 8.6 Interaction with the termination checker

- **Partial definitions aren't recursive** after elaboration, so a partial definition never reaches the termination checker, and there's nothing for the checker to be wrong about.
- **Total code may *mention* partial definitions** freely (`\() -> spin 0` is a total value).
- **A total definition that refers to itself** must still pass the checker. That includes `drain` and anything routed through `step` results.
- **Size-change termination** for groups ([`mutual-recursion.md`](mutual-recursion.md) §6) is unaffected. A partial group becomes one `pfix` over a sum.
- **Choice of mode.** Should a definition declared `{Partial}` that *does* pass the termination checker be translated with `pfix` (one `Later` per call) or as ordinary recursion? Uniform `pfix` makes fuel counts independent of how clever the checker is. That matters once fuel is observable. Recommended: always `pfix`.
- **Test.** A `{Partial}`-free definition whose only recursive call goes through a `Delay` (`step` result) is refused.

### 8.7 Positivity and stored partial functions

- **Partial functions as data.** Storing them is fine: `State (Nat -> {Partial} Nat)` holds `Delay`-returning functions, and running one makes the user partial.
- **A data type recursing through `Delay`** (`type Bad = MkBad (Delay op res Bad)`) is refused as a nested occurrence. Delay's argument is positive in the model, so this can be relaxed later. Nested occurrences are refused today anyway.
- **`Cell`-style knots through `Partial`.** An ability whose response type mentions `Delay` over its own signature is still a self-referential type function, which the kernel refuses as before (`examples/soundness/cell-result.sw`).
- **Test.** `Bad`, and `Cell` with a `{Partial}` stored function.

### 8.8 Foreign and host code

- **Foreign functions.** A foreign function that may not return is declared `{Partial}`. In the core it's a `Delay` whose step is a host call. Declaring it total is a tracked `assume` (DESIGN.md §5 rule 6).
- **Blocking.** A host request may block inside one step. Steps bound work, not time (DESIGN.md §3, `IO` row).

## 9. Staging

**Stage 0: prototype, no kernel change.**
- Build `Machine` (§6.2, 2c) in a test file, with `runFor`, `bind` and an `IO` loop driven by a scripted runner, to settle the fuel semantics and the API.
- Add the must-reject tests from §8 that apply today: `drain`, a `Partial` handler, `Cell` through partial functions, which are rejected for unrelated reasons today.
- **Optional** if `Partial` stalls: option 5b (the runtime drives a total step function) for `main` only.

**Stage 1: `Partial` that only the runtime runs.**
- Kernel: §7.2.
- Elaborator: §7.3, including `Partial` as a mode, `Rec` translation, `lift` subsumption, and the handler restriction.
- Runner and playground: §7.4.
- Driver-level step-budgeted tests.
- `adder.sw` loses its fuel; the four programs of §4 become examples.
- The DESIGN.md rules this changes:
  - rule 4 becomes "`Partial` has no operations; no handler may have it in its residual row";
  - rule 5: tests use step budgets;
  - rule 7 stays.

**Stage 2: bounded observation.**
- `step` becomes a kernel constant with the §7.4 rules, after the reviewer has checked §7.7.
- In the prelude:

  ```
  runFor : Nat -> Delay op res a -> Comp op res (Maybe a)
  runFor 0        d = Done Nothing
  runFor (Succ n) d = bind (step d) (afterStep n)

  afterStep : Nat -> Next a (Delay op res a) -> Comp op res (Maybe a)
  afterStep n (Now x)    = Done (Just x)
  afterStep n (Later d') = runFor n d'
  ```

  This is structural on `n` (a mutual pair, so it needs the mutual-recursion work, or an inlined helper), with operations free.
- `withFuel n f = runFor n (f ())` is the generic `withFuel` DESIGN.md postponed (§16, question 10). `simulateFor n` is `simulate` after `runFor`.
- Tests may use `Partial` through `withFuel`.

**Stage 3 (research): handlers with `Partial` in the residual row.** `interp`-style (§8.4) for `State` and `Abort`, so the interpreter in §4 can use `Abort` around partial evaluation.

**Later.** The JS runtime and stepper exports (§7.5); partiality polymorphism (§10, question 3).

## 10. Open questions for the reviewer

1. **The stage 2 argument (§7.7).**
   - Is "every function invoked by `step` receives only values built before the `pfix` being unfolded" the right invariant?
   - What's the cleanest proof? A reducibility argument with `Delay` read as the final coalgebra, or a step-indexed model?
   - Is there a counterexample through `mapSig`, or through a `bindD` continuation that closes over a `Delay` built from the same `pfix` at an *earlier* argument?
2. **`step` in conversion.** Should stage 2 let the type checker compute `step` on closed terms, so `rfl` proves `runFor 200 (collatzSteps 27) = Done (Just 111)`? Or should `step` stay neutral in conversion and run only in run-mode evaluation (tests)? If conversion computes it, does it still terminate on open terms?
3. **Partiality polymorphism.**
   - Is excluding `Partial` from row variables acceptable at first?
   - Later, a function polymorphic in partiality could take a type-level `Bool`, with `Eff False = Comp` and `Eff True = Delay` and `bind`/`lift` defined by cases. Koka gets this for free because `div` is just a label [K2]. Is there a better encoding when effects are data?
4. **Stage 3 handlers.** Is `interp` with a state- or exception-passing carrier enough for the realistic cases (`runState`, `toMaybe` around partial code)? Is there a known class of deep handlers that stays productive over `Delay` without `▷`?
5. **`Rec` and dependent results.** `pfix`'s `B : A -> Type` makes the recursion signature's response depend on the request. Does the mutual-group encoding (sum of members, `B` by member) need anything beyond what `RecRes` gives?
6. **Productive loops.** Should a loop that performs an `IO` operation before every recursive call (`cat`) be total rather than `Partial`? That's the Hancock–Setzer/ooAgda view [T2] and Idris' `InfIO` [D5]. It would need a separate "guarded by an operation" check, and it changes what DESIGN.md §3 promises: "finitely many operations".
7. **JS exports of partial functions.** Is a stepper object the right boundary, or should partial functions simply not be exportable?
8. **Fuel accounting.** One unit per recursive call, with operations free. Is there a reason to charge operations, as draft 1 suggested?

## What I couldn't verify

- **No proofs.** §7.7's stage 2 argument is an outline. I haven't checked that the M-type for `X ↦ Comp op res (Next a X)` is constructed exactly by [M1] (I read the abstract only), or that coiterating the stack coalgebra gives `pfix` the equation in §7.4.
- **Nothing was run.** No code in this note has been compiled. The `pfixBad` loop in §8.3 is reasoned, not executed.
- **Read only in abstract or snippets:** Nakano [G1], Atkey and McBride [G2], Bahr, Grathwohl and Møgelberg [G3], Paviotti, Møgelberg and Birkedal [G4], and Veltri and Vezzosi's guarded cubical Agda.
- **Oury's 2008 Coq-Club post** is known only through [C7]'s citation and a mailing-list snippet. The fetch was refused.
- **Agda:** whether `NON_TERMINATING` is allowed under `--safe`.
- **F\*:** how `Dv` code specifically is extracted, and the full list of effect abbreviations (`GTot`, `Lemma`, `ML`).
- **Lean:**
  - the description of the compiled auxiliary for `partial def` comes from reading `src/Lean/Elab/PreDefinition/*.lean`;
  - the LNCS volume numbers for [C3] and [C4] are from memory.
- **Idris 2:** what the `%unsafe` pragma does to callers of `assert_total`. It isn't documented in the pragma reference.
- **Unison:** no positive statement either way about tracking divergence.
- **Universes:** the claim that the existential `Machine` encoding needs `Type 1` and climbs with nesting is from the kernel's rules (`docs/core.md`: numbered universes, no cumulativity; `Sig : Type 1` in the prelude). I didn't try it.

## Sources

- [C1] V. Capretta, *General Recursion via Coinductive Types*, LMCS 1(2:1), 2005. <https://arxiv.org/abs/cs/0505037>
- [C2] J. Chapman, T. Uustalu, N. Veltri, *Quotienting the Delay Monad by Weak Bisimilarity*, MSCS 29(1), 2019 (conference version ICTAC 2015). <https://strathprints.strath.ac.uk/61728/>
- [C3] T. Altenkirch, N. A. Danielsson, N. Kraus, *Partiality, Revisited: The Partiality Monad as a Quotient Inductive-Inductive Type*, FoSSaCS 2017. <https://arxiv.org/abs/1610.09254>
- [C4] C. McBride, *Turing-Completeness Totally Free*, MPC 2015. <https://personal.cis.strath.ac.uk/conor.mcbride/TotallyFree.pdf>
- [C5] N. A. Danielsson, *Operational Semantics Using the Partiality Monad*, ICFP 2012. <https://www.cse.chalmers.se/~nad/publications/danielsson-semantics-partiality-monad.pdf>
- [C6] A. Abel, J. Chapman, *Normalization by Evaluation in the Delay Monad*, MSFP 2014, EPTCS 153. <https://arxiv.org/abs/1406.2059>
- [C7] A. Abel, B. Pientka, D. Thibodeau, A. Setzer, *Copatterns: Programming Infinite Structures by Observations*, POPL 2013. <https://www.cse.chalmers.se/~abela/popl13.pdf>
- [C8] Rocq reference manual, *Coinductive types*. <https://rocq-prover.org/doc/master/refman/language/core/coinductive.html>
- [I1] L. Xia, Y. Zakowski, P. He, C.-K. Hur, G. Malecha, B. C. Pierce, S. Zdancewic, *Interaction Trees: Representing Recursive and Impure Programs in Coq*, POPL 2020. <https://arxiv.org/abs/1906.00046>; library: <https://github.com/DeepSpec/InteractionTrees>
- [G1] H. Nakano, *A Modality for Recursion*, LICS 2000. <https://lics.siglog.org/2000/Nakano-AModalityforRecursi.html>
- [G2] R. Atkey, C. McBride, *Productive Coprogramming with Guarded Recursion*, ICFP 2013. <https://strathprints.strath.ac.uk/44848/>
- [G3] P. Bahr, H. B. Grathwohl, R. E. Møgelberg, *The Clocks Are Ticking: No More Delays!*, LICS 2017. <https://researcher.itu.dk/en/publications/the-clocks-are-ticking-no-more-delays-reduction-semantics-for-typ/>
- [G4] M. Paviotti, R. E. Møgelberg, L. Birkedal, *A Model of PCF in Guarded Type Theory*, MFPS 2015. <https://researcher.itu.dk/en/publications/a-model-of-pcf-in-guarded-type-theory/>
- [G5] R. E. Møgelberg, M. Paviotti, *Denotational Semantics of Recursive Types in Synthetic Guarded Domain Theory*, MSCS 29(3), 2019. <https://arxiv.org/abs/1805.00289>
- [G6] Agda manual, *Guarded Type Theory*. <https://agda.readthedocs.io/en/latest/language/guarded.html>
- [A1] Agda manual, *Termination Checking* (pragmas). <https://agda.readthedocs.io/en/latest/language/termination-checking.html>
- [A2] Agda manual, *Command-line options*. <https://agda.readthedocs.io/en/latest/tools/command-line-options.html>
- [A3] Agda 2.6.2 changelog. <https://hackage.haskell.org/package/Agda-2.6.2/changelog>
- [A4] Agda issue #1201. <https://github.com/agda/agda/issues/1201>
- [A5] Agda manual, *Coinduction*. <https://agda.readthedocs.io/en/latest/language/coinduction.html>
- [A6] agda-stdlib, `Effect.Monad.Partiality` and `Codata.Sized.Delay`. <https://github.com/agda/agda-stdlib/blob/master/src/Effect/Monad/Partiality.agda>
- [R1] Rocq reference manual, *Vernacular commands* (Guard Checking, `bypass_check`, `Print Assumptions`). <https://rocq-prover.org/doc/master/refman/proof-engine/vernacular-commands.html>
- [D1] Idris 2 tutorial, *Types and Functions*. <https://idris2.readthedocs.io/en/latest/tutorial/typesfuns.html>
- [D2] Idris 2 tutorial, *Theorem Proving* (totality checking). <https://idris2.readthedocs.io/en/latest/tutorial/theorems.html>
- [D3] Idris 2 reference, *Pragmas*. <https://github.com/idris-lang/Idris2/blob/main/docs/source/reference/pragmas.rst>
- [D4] Idris 2 prelude, `Builtin.idr` (`assert_total`, `assert_smaller`). <https://github.com/idris-lang/Idris2/blob/main/libs/prelude/Builtin.idr>
- [D5] Idris 2 tests, *Type-Driven Development* chapter 11, `InfIO.idr`. <https://github.com/idris-lang/Idris2/blob/main/tests/typedd-book/chapter11/InfIO.idr>
- [L1] Lean language reference, *Recursive Definitions* (partial, unsafe, `partial_fixpoint`). <https://lean-lang.org/doc/reference/latest/Definitions/Recursive-Definitions/>
- [L2] Lean 4.17.0 release notes (#6355). <https://lean-lang.org/doc/reference/latest/releases/v4.17.0/>
- [L3] Lean 4.9.0 release notes (#4061). <https://lean-lang.org/doc/reference/latest/releases/v4.9.0/>
- [L4] Lean 4 source, `src/Init/While.lean` at v4.20.0. <https://github.com/leanprover/lean4/blob/v4.20.0/src/Init/While.lean>
- [F1] N. Swamy et al., *Dependent Types and Multi-Monadic Effects in F\**, POPL 2016. <https://fstar-lang.org/papers/mumon/paper.pdf>
- [F2] *Proof-Oriented Programming in F\**, "Divergence, or Non-Termination". <https://fstar-lang.org/tutorial/book/part4/part4_div.html>
- [K1] D. Leijen, *Koka: Programming with Row Polymorphic Effect Types*, MSFP 2014, EPTCS 153. <https://arxiv.org/abs/1406.2061>
- [K2] *The Koka Programming Language* (book). <https://koka-lang.github.io/koka/doc/book.html>
- [K3] Koka standard library, `lib/std/core/types.kk`, `lib/std/core/undiv.kk`. <https://github.com/koka-lang/koka/tree/master/lib/std/core>
- [U1] Unison documentation, *Abilities* and *Abilities and ability handlers*. <https://www.unison-lang.org/docs/fundamentals/abilities/>, <https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/>
- [Y1] Dafny reference manual (§7.1.3 decreases clause; §13.6.1.8 `dafny audit`). <https://dafny.org/dafny/DafnyRef/DafnyRef.html>
- [T1] D. A. Turner, *Total Functional Programming*, JUCS 10(7), 2004, 751–768. <https://www.jucs.org/jucs_10_7/total_functional_programming/jucs_10_07_0751_0768_turner.pdf>
- [T2] A. Abel, S. Adelsberger, A. Setzer, *Interactive Programming in Agda – Objects and Graphical User Interfaces*, JFP 27, 2017. <https://www.cse.chalmers.se/~abela/ooAgda.pdf>
- [T3] R. Ó. Bjarnason, *Stackless Scala With Free Monads*, Scala Workshop 2012. <https://blog.higher-order.com/assets/trampolines.pdf>
- [M1] B. Ahrens, P. Capriotti, R. Spadotti, *Non-wellfounded Trees in Homotopy Type Theory*, TLCA 2015. <https://arxiv.org/abs/1504.02949>

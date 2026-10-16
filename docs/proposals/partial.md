# Proposal: `Partial`

**Status:** draft 3, 15 October 2026. **Stage 1 is implemented** (16 October 2026; [§9.4, As built](#94-as-built-stage-1)). The user approved stage 1 only: partial code is visible in types (`{Partial}`), only the runtime runs it, and proofs are only about the total parts (the "functional core, imperative shell" style). Everything beyond stage 1 is kept as **someday/maybe** (§10), with what each option would need and the external review's specific concerns. Draft 1 was split out of [`abilities.md`](abilities.md) after review found its design unsound (§2). Draft 2 surveyed other systems (§5), compared five designs (§6) and recommended one; an external review checked it. Draft 3 adopts that review's stage-1 fixes, and is backed by an executable model of the runtime rules (`crates/partial-model`, §9.1). The sections before §9.4 are the design as approved; §9.4 says what was built and where it differs.

This note is meant to be read without knowing the codebase: §1 describes the parts of Stitchwort it touches, checked against the source at commit `0fbec9d`. Claims about other systems cite their sources ([Sources](#sources)). Anything not verified is marked **unverified**; [What I couldn't verify](#what-i-couldnt-verify) lists the gaps.

## Contents

0. [Summary](#0-summary)
   - [Changes since draft 2](#changes-since-draft-2)
1. [Background: Stitchwort today](#1-background-stitchwort-today)
2. [Why draft 1 didn't work, and the general lesson](#2-why-draft-1-didnt-work-and-the-general-lesson)
3. [Goals and non-goals](#3-goals-and-non-goals)
4. [Motivating programs](#4-motivating-programs)
5. [How other systems do it](#5-how-other-systems-do-it)
6. [Options](#6-options)
7. [The proposal: stage 1](#7-the-proposal-stage-1)
8. [What can go wrong](#8-what-can-go-wrong)
9. [Building stage 1](#9-building-stage-1)
10. [Someday/maybe](#10-somedaymaybe)
11. [The review's answers](#11-the-reviews-answers)
12. [What I couldn't verify](#what-i-couldnt-verify)
13. [Sources](#sources)

## 0. Summary

**In plain words.** A function that might run forever says `{Partial}` in its type, and so does everything that calls it. Inside the compiler, a partial function doesn't call itself. Each place where it would recurse becomes a *request* ("please run me again on this argument"), so the function's body is an ordinary, total piece of code that the existing checker checks as usual. Requests are tied together into a possibly endless loop only by one new built-in type, `Delay`, which the type checker can't look inside. Only `stitchwort run` and the playground actually run a `Delay`, one step at a time. Total code can never wait for a `Delay` to finish, so a partial function can't hide inside a total one. Proofs are about the total parts: write the logic as total functions, prove things about those, and keep the partial "shell" thin.

**For the reviewer.** Stage 1 combines McBride's `General` [C4] with Capretta's delay monad [C1]:
- A partial definition is elaborated to a *description*: a total function `(x : A) -> Delay (Plus (Rec A) op) (PlusRes (RecRes B) res) (B x)` whose recursive calls are operations of a private recursion signature `Rec A`.
- A new opaque kernel type former `Delay op res a`, with constants `now`, `lift`, `bindD`, `mapSig` and `pfix`, ties the knot: `pfix` turns a description into the recursive function.
- `Delay` has **no eliminator and no computation rules in the kernel**. Consistency holds because every `Delay op res a` can be read as a one-element set. That argument covers the logic only; that the runtime runs the intended program is a separate, tested obligation (§7.8).
- The runtime gives `Delay` its meaning by `step : Delay op res a -> Comp op res (Next a (Delay op res a))`, specified by equations (§7.4) with explicit suspended states. **Each recursive call is exactly one `Later` ("tick")**; entering a partial function and finishing cost none.
- `step` describes host requests and never performs them; only the runner does.
- Helpers that receive a recursive function as a callback must be polymorphic in the rest of the row (`{Partial | e}`). That's an explicit restriction with its own diagnostic (§7.3).
- Stage 2 (total code observing a `Delay` with fuel), handlers over `Delay`, promotion to total, and the rest are someday/maybe (§10). Stage 1 doesn't depend on any of their arguments.

### Changes since draft 2

| Draft 2 | Draft 3 | Where |
|---|---|---|
| Stage 1 recommended, stage 2 planned, stage 3 research | Stage 1 is the proposal (approved). Stages 2 and 3, promotion to total, equivalence, productive loops and JS stepper exports are someday/maybe, each with what it needs and the review's concerns | §7, §10 |
| `addLines` passed to a helper typed `(Nat -> {IO, Partial} Nat)` | That can't be translated: the callback makes requests in a private signature. Helpers receiving recursive callbacks must be polymorphic in the residual row, with an actionable diagnostic; §4's example is rewritten | §4, §7.3.4 |
| "Each self-call `f e` is replaced by `recur e`" | Every reference is translated: saturated calls, partial applications, bare references, callbacks under lambdas and siblings in a group. Arguments are packed (fixed parameters shared, changing ones in the request); non-uniform polymorphic recursion is out of scope. A recursive reference can't escape its definition | §7.3 |
| Two ticks per recursive call (`pfix` and the request each inserted a `Later`), contradicting "one unit per call" | One tick per recursive call. The equations, the model and the examples agree: Collatz 27 takes 111 ticks | §7.4.3 |
| `Done (Later (tie f (f x)))`: ambiguous under strict evaluation | `pfix f x` is a suspended state; building it runs nothing. Full equations for `tie` and `resume`, which preserve ticks exactly | §7.4 |
| "A partial definition never reaches the termination checker" | "The translated description and wrapper undergo ordinary kernel checking; the translation removes unrestricted source recursion by replacing it with requests" | §7.3.7, §8.6 |
| Consistency argument | Kept, qualified: it doesn't establish the interpreter's correctness, which is a separate semantics-preservation obligation, tested | §7.8 |
| Each step is "one budgeted operation" | Runner policies (work per step, total work, output, cancellation) are separate from semantic ticks | §7.5 |
| "Exports are pure, so no generated JS needs `Delay`" | An explicit extraction policy: `Delay` values are erased to one token, justified by the one-element model; exports whose types mention `Partial` are refused | §7.6 |
| A foreign function's `Delay` "steps by a host call" | `step` describes host requests and never performs them; a possibly non-returning foreign function is an operation of a host signature | §7.4.5, §8.8 |
| Proof story: decreasing requests give a total version | Narrowed: stage 1 proves things about total code only. Promotion to total is someday/maybe, and decreasing requests aren't enough on their own | §7.7, §10.2 |
| `rfl : collatzSteps 1 = now 0` "true at runtime" | "Same eventual result"; no `Delay` equation beyond syntactic identity | §8.5 |
| Agda `NON_TERMINATING` under `--safe`: unverified | Incompatible with `--safe` [A7] | §5.6 |
| Partiality-invisible systems "give no guarantee about programs" | Idris does check totality, and total functions may not call non-total ones [D2]. Its mechanism differs, but it's a program guarantee | §5.12 |
| Stage 0: a `Machine` prototype in the prelude | Stage 0 was done as a standalone Rust model of the runtime rules, with the review's test table | §9.1 |
| Questions for the reviewer | The review's answers, and where this draft stands | §11 |

## 1. Background: Stitchwort today

Stitchwort is a small, strict, pure, dependently typed language written in Rust, built for fun and to explore ideas. A large elaborator (`crates/elab`) turns surface syntax into a small core, and a separate kernel (`crates/core`) re-checks every declaration. Only the kernel is trusted. Programs extract to JavaScript (`crates/js`), and a playground runs the compiler as WebAssembly (`crates/web`).

**The guarantee the user cares about most:** a function whose type doesn't mention `Partial` really terminates, including everything it calls, with no escape hatch. Lean is the motivating counterexample: its `partial def` is invisible in types, so ordinary code can call one and hang (§5.4). DESIGN.md §2 states it as principle 1: "No `Partial`, no divergence… No annotation, attribute or handler can quietly remove it." Principle 2: "Checking never runs effects."

**The kernel** (from [`mutual-recursion.md`](mutual-recursion.md) §1, which describes it in more detail):
- data types with parameters but no indices, strict positivity, numbered universes without polymorphism or cumulativity, and an impredicative `Prop`;
- definitions are case trees, checked by a structural termination checker. The checker accepts if one parameter position decreases in every recursive call. Size-change termination is built for single definitions; function groups and forward references are being added ([`mutual-recursion.md`](mutual-recursion.md));
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

**Goals (stage 1).**
1. **Visible in types.** A function that may not terminate has `Partial` in its row (`Nat -> {Partial} Nat`), and calling one makes the caller `Partial`. There's no `assert_total`, `TERMINATING` or `pretend-no-div`. Declaring a foreign function total remains a tracked `assume` (DESIGN.md §5 rule 6).
2. **Ordinary functions stay total.** A function whose type has no `Partial` terminates, everything it calls included: the same guarantee as today, with the same proof.
3. **Only the runtime runs partial code.** That means `stitchwort run` and the playground's Run button.
4. **The type checker never runs partial code.** It never unfolds a partial definition while comparing types.
5. **Proofs are about the total parts.** No proof of `P` can be obtained by running something that might not finish. The intended style is "functional core, imperative shell": the logic lives in total functions, which can be proved about, and the partial shell (`main`'s loop, a server's loop, an interpreter's driver) is thin.
6. **The motivating programs (§4) are easy to write**, without a fuel argument, and keep working with other abilities as far as is safe.
7. **A small trusted addition**, with a consistency argument a reviewer can check.

**Non-goals (stage 1).** Each is someday/maybe (§10), not rejected:
- Observing a `Delay` from total code, even with fuel, and so any property of partial programs ("if it finishes, the answer is right"). §10.1.
- Turning a partial function into a total one by proving it terminates. §10.2.
- Proving two partial programs equivalent (bisimilarity). §10.3.
- Handlers with `Partial` in their residual row (`runState` around a partial loop). §10.4.
- Distinguishing *productive* interactive loops from silent divergence. Agda and Idris treat `cat` as total because it does I/O between iterations [T2, D5]. Here it's `Partial`. §10.5.
- Exporting partial functions to JavaScript. §10.6.
- General user-defined coinductive types (streams, infinite trees). §6.2 discusses why they're a larger step.
- Wall-clock limits as part of the semantics. Runner policies bound work, output and time (§7.5), but a host request may block.

## 4. Motivating programs

These are written in Stitchwort syntax as it would be with `Partial`. The surface language has no `case` expression yet, so helpers do the matching.

**1. A `main` that reads until end of input.** This is `adder.sw` without its fuel:

```
-- Adds up numbers, one per line, until an empty line or the end of input.
addLines : Nat -> {IO, Partial} Nat
addLines total = step total (readLine ()) addLines

-- As in adder.sw, but `more` may now be partial. `| e` is needed because
-- `addLines` passes itself (§7.3.4).
step : Nat -> Maybe Text -> (Nat -> {IO, Partial | e} Nat) -> {IO, Partial | e} Nat
step total Nothing  more = total
step total (Just l) more =
  if textIsEmpty l then total else stepNumber total l (textToNat (textTrim l)) more

main : () -> {IO, Partial} ()
main u =
  let total = addLines 0
  print ("The sum is " ++ natToText total)
```

- `step` and `stepNumber` aren't recursive. They're total functions that mention `Partial` only because their argument `more` may be partial.
- `addLines` passes itself to `step` unapplied, which the termination checker refuses today. Under `Partial`, the reference becomes a request-making callback (§7.3.3).
- **Draft 2's version didn't type-check under its own translation.** With `step : … -> (Nat -> {IO, Partial} Nat) -> …`, the callback's row is fixed, so it can't make `addLines`'s private recursion requests. The review found this [RV §1]. The `| e` is the fix; without it the elaborator reports E-PARTIAL-CALLBACK (§7.3.4) and says to add it.

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

`serve` and `respond` are a recursive group (they call each other), so this needs the mutual-recursion work (§9.3). The state is an explicit argument. With `runState` around a partial computation, it could be an ability instead. That's a handler with `Partial` in its residual row, which stage 1 excludes (§7.3.8, §10.4). `record` and `report` are total, so they're the parts to prove things about.

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
apply (Lam b) v = eval (subst 0 v b)   -- subst is total, and provable about
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

### 5.6 Agda [A1–A7]

- **Pragmas.**
  - `{-# TERMINATING #-}` "switches off termination checker… and marks them as terminating"; it "cannot be used in --safe mode" [A1].
  - `{-# NON_TERMINATING #-}` is "a safer version of TERMINATING which doesn't treat the affected functions as terminating": "NON_TERMINATING functions do not reduce during type checking", but "do reduce at run-time" [A1].
  - Neither shows up in types. Both are incompatible with `--safe`: the manual's list of unsafe features includes "`--no-termination-check` and pragmas `TERMINATING` and `NON_TERMINATING`; give loopy programs any type" [A7]. (Draft 2 had this as unverified.)
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
| Agda [A1] | pragma / codata | no (pragmas); yes (codata) | no for `NON_TERMINATING` | `TERMINATING`, `NON_TERMINATING` (neither under `--safe` [A7]) | coinductive `IO` |
| Rocq [R1] | not supported | – | – | `bypass_check`, listed by `Print Assumptions` | ITrees |
| F* [F1] | `Div` effect | yes | no: specs are `Tot`/`GTot` | top-level effects warn only | effect lattice |
| Koka [K1] | `div` row label, inferred | yes | n/a | `pretend-no-div` (unsafe) | ordinary row polymorphism |
| Dafny [Y1] | `decreases *` on methods | in the signature | functions must terminate | none | n/a |
| Guarded TT [G3] | `▷` | yes | yes (normalising) | none | research |

Three patterns stand out:
- **Systems where partiality is invisible in function types** (Lean, Idris, Agda pragmas) keep the *logic* consistent by refusing to unfold. Their program guarantees differ: Lean's `partial def` gives none, while Idris checks totality and requires total functions not to call non-total ones [D2], a guarantee that propagates through references rather than types (and has an untracked `assert_total`).
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

**JS, `main`, proofs.** `main`'s tree, with its signature and dispatcher, would be run by the same loop as today, extended to dispatch `Recur`. Proofs about descriptions are ordinary proofs, and a Bove–Capretta domain predicate gives totality by proof [C4, §8]. That's attractive; §10.2 says what carrying it over to `Delay` would need.

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

**2b. One built-in type with a closed set of primitives.** No user codata. The kernel adds `Delay op res a` and a few constants (§7.2). Corecursion is possible only through those constants, so no guardedness checker is needed, provided the constants can't be used to force their own knot (§8.3). This is the proposal (§7).

**2c. The coalgebra encoding, with no kernel change.** A final coalgebra can be represented by an existential state and a step function:

```
type Machine (op : Type) (res : op -> Type) (a : Type) : Type 1 =
  | MkMachine (s : Type) (start : s) (next : s -> Comp op res (Next a s))
```

This is draft 1's "resumable machine" experiment, packaged.
- **Soundness.** `next` is total and finite, and the termination checker refuses any function that runs a machine to the end. Fuel-bounded running is structural on the fuel.
- **The catch.** `Machine … : Type 1`, and `bind` of two machines needs a state that contains machines, so nesting climbs universes. Without universe polymorphism it's impractical as the language's representation.
- **Use.** It *is* a cheap way to prototype the API and fuel semantics before touching the kernel. In the event, stage 0 was done as a standalone Rust model instead (§9.1).

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
| Handlers with `Partial` in the residual row | broken semantics | yes (with productive handlers) | **excluded (someday/maybe)** | excluded | yes | n/a | n/a |
| Fuel-bounded observation | yes | yes | **someday/maybe** | yes | no | no | no |
| Checker never runs partial code | yes | no (unfolds codata) | **yes** | yes | yes | yes | yes |
| Main risk | ergonomics | soundness of new machinery | **the translation's reach (§7.3.4)** | universes | size | invisible | covers only `main` |

## 7. The proposal: stage 1

Option 1's descriptions combined with option 2b's built-in type. McBride's `delay` interpretation [C4, §6] becomes the one new kernel constant, `pfix`, with no computation rules.

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

These are ordinary prelude data types. `Next` isn't used by the kernel in stage 1; it names what the runtime's `step` returns (§7.4).

### 7.2 The kernel's additions

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

- **No computation rules.** An application of one of these constants is a neutral term. Conversion compares neutral terms structurally and never unfolds anything.
- **No elimination.** There's no `case` on `Delay`, because it isn't a data type, and no eliminator into any other type.
- **Positivity.** A data type whose field mentions the type being declared inside `Delay`'s arguments is refused, as nested occurrences such as `List D` already are.
- **Termination.** No change, and no exemption (§7.3.7).

### 7.3 Elaboration: the request translation

#### 7.3.1 Mode

`A -> {Partial | ρ} B` translates to `A -> Delay op_ρ res_ρ B`, where `ρ` is the rest of the row. Without `Partial`, the translation is `A -> Comp op_ρ res_ρ B`, as today. So `Partial` isn't a signature label. It's a *mode* that selects `Delay` instead of `Comp`.

- **Calling a partial function** from partial code is `bindD`. Calling one from total code is a type error: goal 1.
- **A total computation** used where a partial one is expected is wrapped with `lift`. For a computation that's one constructor around a well-founded tree. For a *function* the wrapper goes inside: a total callback `f : X -> {ρ} Y` passed where `X -> {Partial | ρ} Y` is expected becomes `\x -> lift (f x)` [RV §8].
- **Another partial function called inside a description** is embedded with `mapSig sigRight`, so its operations pass through the description's private signature untouched.

#### 7.3.2 Which definitions use `pfix`

A definition whose type has `Partial` and which refers to itself, or a recursive group (§9.3) whose members do, becomes a description plus a wrapper. Partial definitions that don't refer to themselves are ordinary definitions returning a `Delay`.

A `{Partial}` definition that *would* pass the termination checker is still translated with `pfix`. Uniform translation keeps tick counts (§7.4.3) independent of how clever the checker is, and the user's annotation says what they meant.

#### 7.3.3 Every reference to a recursive member

Inside the body, *every* occurrence of a member of the definition's own recursive group is translated, not only the syntax `f e` [RV §1]. With `pack` building the request's argument (§7.3.5) and `inj_g` selecting the member in a group:

| Source occurrence (inside the group's bodies) | Translation |
|---|---|
| Saturated call `g e₁ … eₙ` | `recur (inj_g (pack e₁ … eₙ))` |
| Partial application `g e₁ … eₖ`, `k < n` | `let a₁ = e₁ … aₖ = eₖ in \xₖ₊₁ … xₙ -> recur (inj_g (pack a₁ … aₖ xₖ₊₁ … xₙ))` |
| Bare reference `g` | `\x₁ … xₙ -> recur (inj_g (pack x₁ … xₙ))` |
| Any of these under a lambda, inside an argument or a `let` | The same, wherever it occurs |
| In a type | Refused: a member's result is a `Delay`, which no type can compute with anyway |

- `n` is the member's *entry arity*, the same number the mutual-recursion work defines once and every consumer uses ([`mutual-recursion.md`](mutual-recursion.md) §5.3).
- A partial application's supplied arguments are `let`-bound *outside* the new lambda. Under strict evaluation they're evaluated once, where the application was, as in the source. This is the evaluation-order concern that made the mutual-recursion review refuse automatic eta-expansion for total groups (§6.3 there). Here the expansion is safe because it changes nothing about termination: building a request runs nothing.
- `recur y` is `lift (Call (L (Recur y)) Done)`. Its row is the private recursion signature plus `ρ`. Every translated reference therefore has a type of the form `X -> Delay (Plus (Rec A) op_ρ) … Y`.

#### 7.3.4 The higher-order restriction

A translated reference's row contains the private signature `Rec A`, which no type outside the definition can name. So:

> **A recursive member can flow only to places whose type is polymorphic in the rest of the row.** A helper that receives a recursive callback must have a type such as `useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat`. The description instantiates `e` with its private signature (plus `ρ`, up to the elaborator's usual row reordering by an inserted `mapSig`).

The review's example is the smallest case:

```
useP : (Nat -> {Partial} Nat) -> Nat -> {Partial} Nat     -- monomorphic: refused below
useP k n = k n

loop : Nat -> {Partial} Nat
loop n = useP loop n
```

`useP`'s callback type is `Nat -> Delay ∅ Nat`; the translated `loop` is `Nat -> Delay (Plus (Rec Nat) ∅) Nat`. Wrapping `useP`'s *result* in `mapSig sigRight` doesn't help: the problem is its *argument*. The error:

```
[E-PARTIAL-CALLBACK] `loop` can't be passed to `useP` here
  loop n = useP loop n
                ^^^^ `loop` calls itself, so as a value it makes requests that
                     only `loop`'s own definition can answer
  = `useP`'s parameter has the fixed row {Partial}
  = make `useP` polymorphic in the rest of the row:
      useP : (Nat -> {Partial | e} Nat) -> Nat -> {Partial | e} Nat
```

The diagnostic names the helper and the parameter, and suggests the type. When the helper is a library function the user can't change, it says so and suggests the polymorphic variant if one exists (`mapP` for `map`).

**Escapes.** A translated reference can't leave the description, because nothing outside it answers its requests:
- **Returned:** `retry n = \x -> retry (n - 1) x`, where the result type `Nat -> {Partial} Nat` has no private signature in it.
- **Stored in returned data:** a record of callbacks referring to the definition, returned as the result.
- **Passed to a polymorphic helper whose result keeps it**, e.g. `wrap : (Nat -> {Partial | e} Nat) -> Box e`, whose result is then returned.

Each is a type error in the core (the result type `B` has no `Rec A`), reported as E-PARTIAL-ESCAPE: "a recursive call to `retry` can't escape `retry`'s definition; move the loop into its own definition and return a closure over that". Callbacks *stored in data that's used inside the description*, such as a record of handlers passed to a row-polymorphic driver, are fine. So are closures over *other*, already-defined partial functions, returned or stored anywhere. The model checks all three (§9.1).

**Why not repair this by handing the description its own tied function?** For example, a request `Self` answered with `pfix f`. That's sound in stage 1, since nothing can observe a `Delay`. But it gives a description access to its own knot, which is exactly what makes §8.3's attack possible once total code can observe a `Delay` (§10.1). Keeping the knot out of descriptions keeps stage 2 open [RV §1].

#### 7.3.5 Packing arguments

- **Fixed parameters** are shared. A parameter that every recursive reference passes unchanged (the same variable, in the same position) stays outside `pfix`, captured by the description. `firstFrom`'s `p` is one. Type and universe parameters are always treated this way.
- **Changing arguments** are packed into `A`: a tuple, or a dependent pair when later argument types depend on earlier ones. `B` is computed from the packed value.
- **A group:** `A` is a sum over the members of their packed arguments, and `B` is computed by cases on the member. That's ordinary data, matching ITrees' `mrec` [I1]. `RecRes B` is enough for this [RV §1].
- **Non-uniform polymorphic recursion** is out of scope: a recursive reference that changes a type argument (`f : [a : Type] -> … ; f … = … f [List a] …`) is refused with E-PARTIAL-NONUNIFORM. Packing a type into `A` would put `A` in `Type 1`, and without universe polymorphism the request signature wouldn't fit `Delay`'s `op : Type`.

Using the example from §4:

```
-- Source
firstFrom : (Nat -> Bool) -> Nat -> {Partial} Nat
firstFrom p n = if p n then n else firstFrom p (n + 1)

-- Core (sketch): `p` is fixed, `n` is packed (here, it's the whole of A)
firstFromBody : (Nat -> Bool) -> (n : Nat) -> Delay (Plus (Rec Nat) ∅) … Nat
firstFromBody p n = if p n then now n else recur (n + 1)

firstFrom : (Nat -> Bool) -> Nat -> Delay ∅ … Nat
firstFrom p = pfix (firstFromBody p)
```

#### 7.3.6 Rows

- **Row variables range over `Partial`-free rows.** `Partial` is a mode, not a label, so a row variable can't contain it. A function polymorphic in its callback's effects, `map : (a -> {e} b) -> List a -> {e} List b`, can't be given a partial callback. A library provides `mapP : (a -> {Partial | e} b) -> List a -> {Partial | e} List b`, and total callbacks fit it through the `lift` wrapper.
- A private recursion signature *is* an ordinary signature, so `e` may be instantiated with it. That's what makes §7.3.4's restriction workable.
- Being polymorphic in partiality itself, as in Koka, is someday/maybe (§10.7).

#### 7.3.7 Kernel checking: no exemption

**The translated description and wrapper undergo ordinary kernel checking. The translation removes unrestricted source recursion by replacing it with requests.** Nothing about a partial definition bypasses the kernel [RV §2]:
- The description is an ordinary, non-recursive definition. It's type-checked, and the termination checker sees it like any other.
- If a buggy elaborator left a reference to a member in the core, it would be a reference to the wrapper being defined: a self-reference, which the termination checker refuses, or a reference to a declaration that isn't final yet, which admission refuses ([`kernel-admission.md`](kernel-admission.md), [`mutual-recursion.md`](mutual-recursion.md) §5.2).
- No new termination principle is needed in stage 1.

#### 7.3.8 Handlers

- A `handle` whose *clauses* call partial code is fine: its carrier is a `Delay`, and the fold is over a well-founded `Comp`.
- A `handle` whose *handled computation* is partial, meaning `Partial` is in the handler's residual row, is refused. So is `Partial` instantiating a handler's row variable. That's DESIGN.md's rule 4 ("only the runtime handles `Partial`"), made precise. The kernel enforces it independently: a handler is a fold over `Comp`, and there's nothing to fold in a `Delay`.

### 7.4 The runtime semantics

Stage 1 doesn't put `step` in the kernel. These equations are the specification that the evaluator's run mode implements, and that `crates/partial-model` transcribes literally (`src/reference.rs`).

#### 7.4.1 Values and suspended states

Stitchwort is strict, so the equations must say when user code runs [RV §5]:
- **Values a program can build** are applications of the five constants. Building one evaluates its arguments to values, and nothing else. In particular **`pfix f x` stores `f` and `x` without applying `f`**: the body runs only when the value is stepped. A `bindD d k` stores `k` without calling it.
- **Internal states** that only the runtime builds:
  - `tie f d`: the description `d` (over `Plus (Rec A) op`) with its requests answered by `f`;
  - `resume s`: a segment `s` turned back into a `Delay`.

  `tie` and `resume` are not kernel constants. In stage 1 they never reach the kernel: `step` is called only by the runner, and its results are never quoted back into terms.

#### 7.4.2 The equations

A *segment* is what one step returns: `Comp op res (Next a (Delay op res a))`, a well-founded tree of operations ending in `Now v` or `Later rest`.

```
step : Delay op res a -> Comp op res (Next a (Delay op res a))

step (now v)       = Done (Now v)
step (lift c)      = mapLeaves c
step (bindD d k)   = bindSeg k (step d)
step (mapSig m d)  = mapSeg m (step d)
step (pfix f x)    = tieSeg f (step (f x))        -- enter the body: no tick
step (tie f d)     = tieSeg f (step d)
step (resume s)    = s                            -- ticks in s are kept, none added

mapLeaves (Done v)            = Done (Now v)
mapLeaves (Call o r)          = Call o (\y -> mapLeaves (r y))

bindSeg k (Done (Now v))      = step (k v)
bindSeg k (Done (Later d'))   = Done (Later (bindD d' k))
bindSeg k (Call o r)          = Call o (\y -> bindSeg k (r y))

mapSeg m (Done (Now v))       = Done (Now v)
mapSeg m (Done (Later d'))    = Done (Later (mapSig m d'))
mapSeg m (Call o r)           = Call (m.op o) (\y -> mapSeg m (r (m.res o y)))

tieSeg f (Done (Now v))          = Done (Now v)
tieSeg f (Done (Later d'))       = Done (Later (tie f d'))
tieSeg f (Call (R o) r)          = Call o (\y -> tieSeg f (r y))
tieSeg f (Call (L (Recur y)) r)  = Done (Later (bindD (pfix f y) (\v -> tie f (resume (r v)))))
                                   -- the one tick for this recursive call
```

**Every case of `tie` and `resume`:**
- `tie f` passes `Now` through, keeps an inner `Later` as exactly one `Later` (re-wrapping its rest in `tie f`), forwards every non-recursion operation with its reply unchanged, and turns a recursion request into one `Later` whose rest runs the callee and then the caller's continuation under `tie f` again.
- `resume s` returns `s` unchanged, so a `Later` in the rest of a caller's segment stays exactly one `Later`. Nothing is discarded or duplicated.
- The callee `pfix f y` and the caller's continuation `r v` are stored, not evaluated, inside the `Later`'s rest: a request suspends *before* the callee's body runs.

**Well-founded, not finite.** A `Comp`'s continuation can branch on infinitely many replies and have arbitrarily long finite paths, so a segment is a *well-founded* tree, not a finite one [RV §5]. Every path through one step ends. The cost of one step isn't bounded in advance, which is why the runner has policies (§7.5).

#### 7.4.3 The fuel rule: one tick per recursive call

Draft 2's `pfix` equation was `step (pfix f x) = Done (Later (tie f (f x)))`, and its request case also produced a `Later`, so every recursive call cost two ticks, plus one for entering. The review computed the consequences [RV §4], and the model reproduces them exactly (`counts_table` in `crates/partial-model/tests/table.rs`).

Draft 3's rule:
- **A tick is a recursive call.** Each recursion request, to the definition itself or to a sibling in its group, produces exactly one `Later`.
- **Entering a partial function is free**, and so is a partial function that doesn't recurse. `immediate n = n`, declared `{Partial}`, steps straight to `Done (Now n)`.
- **Operations are free**: they're `Call`s inside a segment.
- **Nested partial functions** add their own ticks. A request inside a callee is answered by the callee's `tie`, and the caller's `tie` sees its `Later` and keeps it as one.

So a computation that makes `n` recursive calls in all has exactly `n` `Later`s, and the runner calls `step` `n + 1` times. Measured on the model, against draft 2:

| Program | Draft 2: `Later`s | Draft 2: observations | **Draft 3: `Later`s** | Draft 3: observations |
|---|---|---|---|---|
| Immediate return | 1 | 2 | **0** | 1 |
| One recursive request | 3 | 4 | **1** | 2 |
| Two recursive requests | 5 | 6 | **2** | 3 |
| `collatzSteps 1` | 1 | 2 | **0** | 1 |
| `collatzSteps 27` | 223 | 224 | **111** | 112 |
| `fib 10` (nested, non-tail) | 353 | 354 | **176** | 177 |

Draft 2's column agrees with the review's model: 2, 4 and 6 observations, and 224 for Collatz 27. 111 is the number of Collatz steps from 27 to 1; `fib 10` makes 177 calls, so 176 are recursive. For mutual recursion, `even 10` takes 10 ticks, and Hofstadter's `F 10` takes 178 (one fewer than its 179 calls, counted directly).

**Should seeing `Now` cost fuel?** That only matters once total code can observe a `Delay` (§10.1). The recommended convention: fuel is the number of `Later`s that may be crossed, and seeing `Now` is free. Then `runFor n d` finishes exactly when `d` makes at most `n` recursive calls: `runFor 111 (collatzSteps 27)` gives `Just 111`, and `runFor 110` gives `Nothing`. Draft 2's question used `runFor 200 (collatzSteps 27) = Done (Just 111)`, which was false under its own rules (224 needed) and is true under these.

**Why not one tick per call, including the first,** as McBride's `delay` does [C4, §6]? It would make every partial function, even one that never recurses, cost a tick to enter, so wrapping total code in a `{Partial}` function would change its count. Counting recursive calls makes the count a property of the recursion, which is what fuel is meant to bound.

#### 7.4.4 The implementation: a machine with heap frames

The equations are recursive, and a direct transcription isn't stack-safe: left-nested `bindD`s and deep non-tail recursion each nest host calls. The run mode instead uses an abstract machine whose pending work is an explicit stack of frames on the heap, in the style of ITrees' `interp_mrec`, where a recursive request extends the pending computation with the requested body and the caller's continuation [I1, RV §3]. In the model (`src/machine.rs`, about 300 lines):
- frames are `Bind k`, `Map m`, `Tie f`, and `Await`: a caller waiting for a recursive call's result, holding its continuation and its own frames;
- an operation leaving the focus is routed outwards through the frames: `Map` translates it (and its reply on the way back), `Tie` answers a recursion request, and anything that reaches the bottom is returned to the runner, unperformed;
- a tail request (the continuation is `Done` and nothing is pending above the `Tie`) pushes nothing, so a loop like `serve` runs in constant frames: measured at 1 frame for a million iterations.

The model checks the machine against the equations on every test program and on 1,200 generated ones: the complete traces (each operation, its reply, and each tick, in order) must be identical. That's the shape of the semantics-preservation test the real implementation needs (§7.8).

The kernel's evaluator is already a stack-safe abstract machine ([`stack-safe-evaluation.md`](stack-safe-evaluation.md)), so this is an extension of it, not a second evaluator.

#### 7.4.5 Host requests: `step` never performs them

**`step` describes host requests; it never performs them** [RV §6]. A segment's `Call`s are data returned to the runner, which performs each one and resumes the segment with the reply. The machine has no access to the host at all.

This settles foreign functions:
- A foreign function that may not return is an **operation of a host signature** (an ability whose operations the runner performs), with `{Partial}` in its type. It's never a `Delay` whose step "is a host call".
- A blocking or non-returning host call can stall only the runner, which is outside the total core, and the runner's cancellation applies (§7.5).
- Declaring a foreign function total remains a tracked `assume` (DESIGN.md §5 rule 6).

In stage 1 this is mostly hygiene, since no total code can step a `Delay`. It's stated now because §10.1 depends on it: a total observer that executed a foreign call inside `step` could hang despite having no `Partial` left in its type [RV §6].

### 7.5 The runner and its policies

The runner (`crates/driver/src/run.rs`) changes little:
- `main : () -> {IO, Partial} ()` is accepted as well as `() -> {IO} ()`, which is lifted.
- The loop calls `step` on the current `Delay`, walks the segment as it walks a `Comp` today (perform each `Call`, resume with the reply), continues with the rest at `Later`, and stops at `Now`.

**Semantic ticks and runner policies are separate** [RV §6]. A tick is part of what a program means (§7.4.3). Policies bound host resources and never change meaning:

| Policy | Bounds | When exceeded |
|---|---|---|
| Work per step | Evaluation steps between two `Later`s (one segment), as today's per-step budget | `E-RESOURCE`: a single step did too much |
| Total work | All evaluation, across steps | `E-RESOURCE` |
| Output | Bytes printed (the playground's 256 KB cap) | Stop, with what was printed |
| Cancellation | The playground's Stop button and 15-second timeout | Stop |
| Tick limit (tests only) | `Later`s | *Inconclusive*, never pass or fail (DESIGN.md §7) |

A small tick limit doesn't make control return promptly: one step may do a lot of total work, perform many operations, or block in a host call. The model's `policies` test exercises each: an endless loop stops at the tick limit, a long total step exceeds the per-step work with zero ticks, an endless printer stops at the output cap, and a cancelled run stops.

**The playground** uses the same runner. It already has the timeout and Stop that an unbounded program needs.

**`simulate`** can't run a partial `main` in stage 1, since that would be a handler with `Partial` in its residual row. Tests of partial programs are driver-level scripted runs with a tick limit.

### 7.6 JavaScript: the stage-1 extraction policy

Exports stay pure (DESIGN.md §12). But "exports are pure, so no JS needs `Delay`" doesn't follow [RV §8]: a pure function can mention a partial one without running it.

```
discard : (Nat -> {Partial} Nat) -> Nat
discard f = 0

answer : Nat -> Nat
answer n = discard collatzSteps
```

The extractor reaches `collatzSteps` from `answer`. The choices are an inert representation, erasure under a justified abstraction, or rejection. **Recommended: erasure.**

- **The rule.** Every expression whose type is a `Delay` is extracted as one constant token, and every function whose result is a `Delay` as a function returning that token. Descriptions are then unreachable and dropped. An export whose *type* mentions `Delay` (it takes or returns a partial function) is refused: E-JS-PARTIAL, "partial functions can't be exported yet".
- **Why it's correct.** It's the consistency model of §7.8 made executable. In stage 1 no total code can tell two `Delay` values apart: there's no eliminator, no computation rule, and no runtime operation on them except the runner's. So every value of `Delay op res a` can be replaced by the same token without changing any observable result of a pure export.
- **What it changes.** Strict evaluation of arguments that only feed a `Delay` is skipped (`discard (collatzSteps (expensive x))` no longer computes `expensive x`). Those computations are total and pure, so the only observable difference is less work, and a `StitchwortResourceError` that could no longer happen.
- **Why not the alternatives.**
  - An *inert representation* (small JS objects for the constants, with no stepper) ships descriptions that nothing can run. It would become the right choice only when JS gets a stepper (§10.6).
  - *Rejecting* reachable partial definitions repeats Idris' coarse propagation through references (§6.4): `answer` is total and should export.
- **When it must be revisited.** If total code ever gets to observe a `Delay` (§10.1), erasure is no longer correct, and the extractor must switch to a real representation. A test should pin this: a must-reject check that the erasure pass refuses to run if the kernel ever registers an eliminator for `Delay`.

### 7.7 What can be proved in stage 1

Stage 1's proof story is narrow on purpose: **proofs are about total code** [RV §7].
- **The total parts are ordinary.** `record`, `report`, `subst` and `textToNat` in §4 are total functions, and their properties are ordinary theorems. Putting the logic there and keeping the partial shell thin is the intended style.
- **A description is a total function**, so pointwise facts that follow by reducing it are provable, for example `collatzBody 1 = now 0` by `rfl`.
- **Nothing more about requests.** A description returns an opaque `Delay`, which can contain calls to other partial functions. Stage 1 has no way to enumerate or interpret the requests a description makes, so "every request is on a smaller argument" can't even be stated in general.
- **Partial definitions are never unfolded in proofs.** `rfl : collatzSteps 1 = now 0` fails, because conversion never unfolds `pfix`. The two have the *same eventual result*. Under draft 3's rule they even step identically (both to `Done (Now 0)`, §7.4.3), but conversion doesn't step.
- **No route from partial to total** in stage 1. A function that turns out to terminate can be rewritten as a total one (with the termination checker's help), but not promoted. §10.2 says what promotion would need.

### 7.8 Why it's sound

**Consistency and totality of `Partial`-free code.**
1. *Consistency.* The kernel only gains an opaque type former and constants with no computation rules. Any model of the existing theory extends by interpreting every `Delay op res a` as a one-element set, and the constants as the only functions into it. None of the constants' types extracts an `a` from a `Delay … a`, so the model doesn't need `a` to be inhabited. That's the important difference from an opaque constant inhabiting `Void` directly, and why no inhabitedness side condition is needed, unlike Lean's `partial` [L1]. Conversion is unchanged on old terms, and new terms are neutral. So no new closed proof of `Void` exists. The review found this argument convincing [RV §2].
2. *Totality.* A `Partial`-free closed term's evaluation is the old evaluation. The only new values it can hold are `Delay` values, and no total function inspects them: there's no `case`, no eliminator and no reduction rule. So the existing argument applies, treating `Delay` values as opaque constants. A total function receiving a `{Partial}` callback can only build bigger `Delay`s with it.
3. *Draft 1's `drain`* has no counterpart. There's nothing to recurse on.

**What this argument does not establish** [RV §2]:
- **That the runtime runs the intended program.** The singleton model says nothing about `step`. That the request translation, `tie` and the runner implement the source program's meaning is a separate *semantics-preservation* obligation. Stage 1 meets it by testing, not proof:
  - the run mode is checked against the equations of §7.4.2, as the model does (identical traces on fixed and generated programs);
  - partial programs' runs are compared with hand-written expected traces (operations, replies and ticks, in order), not just final values;
  - when the stepping rules change, tests that record tick counts must change with them.
- **Anything about stage 2.** Observation by total code needs its own argument (§10.1).

### 7.9 Trusted code

All of these are estimates.

| Where | What | Size |
|---|---|---|
| Kernel (`crates/core`) | `Delay` type former and five constant signatures; neutral treatment; positivity treats `Delay`'s arguments as non-positive positions | ~100–200 lines |
| Evaluator, run mode | `step` as the machine of §7.4.4 (the model's is ~300 lines with comments) | ~300 lines |
| Runner | accept `{IO, Partial}`; loop on `step`; policies | ~60 lines |
| JS extractor | erase `Delay`-typed expressions; refuse exports mentioning `Delay` | ~50 lines |

The kernel lines are trusted for consistency. The run mode and runner are trusted only for "runs what was written": a bug there can make a program behave wrongly, never make the logic inconsistent, and it's covered by the semantics-preservation tests. The elaborator's work is untrusted: the request translation, mode selection, `lift` insertion, and the diagnostics. Getting it wrong produces rejected or wrong-but-total programs, never an unsound one. The kernel enforces the two checks that matter: a handler fold over `Delay` has nothing to fold, and a total type is a `Comp` type.

## 8. What can go wrong

Each pitfall is paired with what prevents it. Each test is a must-reject test in `examples/soundness/` unless it says otherwise. Following the review [RV §9], a must-reject test has to fail *for the intended reason*: tests rejected today merely because `Partial` syntax doesn't exist yet are kept separate from soundness regressions, and their snapshots are re-checked when stage 1 lands.

### 8.1 `drain`, generalised

Any total function that recurses through the endless part of a computation proves `Void`.
- There's nothing to recurse on: `Delay` has no `case` and no eliminator.
- **Test.** A `case` on a `Delay` built by hand (kernel: not a data type); a total function applying `pfix`'s argument to recurse (an ordinary recursive definition, refused by termination).

### 8.2 A handler that "acknowledges every step"

DESIGN.md §5 rule 4 exists for this case. A handler for `Partial` that answered each step and resumed would turn an endless computation into a "total" one.
- `Partial` isn't an ability with operations, so there's nothing to handle. Koka's `div` has no operations for the same reason [K3].
- **Test.** A handler naming `Partial`; a `handle` with `Partial` in its residual row; `Partial` instantiating a handler's row variable.

### 8.3 Forcing the knot

This is the reason for the request form, and why a description never gets its own tied function (§7.3.4). It can't happen in stage 1, where nothing steps a `Delay` except the runner, but it's what any future observer (§10.1) must exclude. Suppose `pfix` gave the description the function being defined:

```
pfixBad : ((A -> Delay B) -> A -> Delay B) -> A -> Delay B
```

If total code could step a `Delay`, a description could step its own recursive call past the `Later`: `f self x = stepTwice (self x)`. Stepping `pfixBad f x` runs `f`, which steps `pfixBad f x`, which runs `f` again, and so on: a single "total" step that never returns. Fuel doesn't help, because every invocation of `f` gets fresh fuel.
- The same shape appears in Coq as the guard condition's ban on eliminating corecursive calls [I1, footnote 3], and in guarded type theory as `▷`, which makes `self x` unavailable "now" [G1, G5].
- **The request form prevents it.** A description has `recur`, which produces a request that only `tie`, inside the runtime, answers.
- **Test.** In the kernel, a hand-built `pfix` whose description mentions `pfix` of itself: that's a recursive definition, refused by the termination checker. In the elaborator, a partial definition never translates a member reference into anything but a request (§7.3.3).

### 8.4 Escaping recursive callbacks

A translated reference makes requests in a private signature. If one escaped its description (returned, or stored in returned data), nothing would answer its requests.
- It can't: the result type `B` doesn't mention the private signature, so the core doesn't type-check, and the elaborator reports E-PARTIAL-ESCAPE (§7.3.4).
- **Tests** (elaborator, with accepted neighbours): `retry n = \x -> retry (n - 1) x` refused, and the same returning a closure over a separately defined partial function accepted; a record of callbacks referring to the definition, returned, refused, and the same record passed to a row-polymorphic driver inside the definition accepted; `loop n = useP loop n` refused with a monomorphic `useP` (E-PARTIAL-CALLBACK) and accepted with a polymorphic one. The model has each of these (§9.1).

### 8.5 Equality and conversion on partial values

- Conversion never unfolds `pfix`, so the checker can't loop on partial code. `rfl : collatzSteps 1 = now 0` fails.
- **Equality.** Syntactically equal `Delay` terms are equal, which every model respects. There's **no eta rule** for `Delay` and no bisimilarity quotient: comparing two `Delay`s by stepping both is bisimilarity, which is undecidable and would make conversion unfold forever. Where this document means "both finish with the same value", it says *same eventual result*.
- **Tests.**
  - `rfl : collatzSteps 1 = now 0` is refused.
  - `Vec Nat (collatzSteps 5)` is a type error (`Delay` isn't `Nat`).
  - A proof of `Void` from `spin () : {Partial} Void` is refused.

### 8.6 Interaction with the termination checker

- **No exemption.** The translated description and wrapper undergo ordinary kernel checking; the translation removes unrestricted source recursion by replacing it with requests (§7.3.7). A malformed translation that kept a recursive reference is refused by the ordinary checks.
- **Total code may *mention* partial definitions** freely (`\() -> spin 0` is a total value).
- **Size-change termination** for groups ([`mutual-recursion.md`](mutual-recursion.md) §6) is unaffected. A partial group becomes one non-recursive description over a sum (§9.3).
- **Test.** A hand-written core description that calls its own wrapper is refused by termination; one that calls a sibling's not-yet-final wrapper is refused by admission.

### 8.7 Positivity and stored partial functions

- **Partial functions as data.** Storing them is fine: `State (Nat -> {Partial} Nat)` holds `Delay`-returning functions, and running one makes the user partial.
- **A data type recursing through `Delay`** (`type Bad = MkBad (Delay op res Bad)`) is refused as a nested occurrence. `Delay`'s argument is positive in the model, so this could be relaxed later. Nested occurrences are refused today anyway.
- **`Cell`-style knots through `Partial`.** An ability whose response type mentions `Delay` over its own signature is still a self-referential type function, which the kernel refuses as before (`examples/soundness/cell-result.sw`).
- **Test.** `Bad`, and `Cell` with a `{Partial}` stored function.

### 8.8 Foreign and host code

- **`step` describes host requests and never performs them** (§7.4.5). A foreign function that may not return is a host operation with `{Partial}` in its type, performed only by the runner. The model checks that `step` returns such a call as data, with the host never invoked, and that only the runner gets stuck on it.
- **Blocking.** A host request may block. The runner's cancellation and timeout apply; steps bound work, not time (DESIGN.md §3, `IO` row).

## 9. Building stage 1

### 9.1 Stage 0, done: an executable model of the rules

`crates/partial-model` is a small standalone Rust crate (no dependency on the kernel; nothing in the compiler uses it) that models stage 1's runtime:
- `delay.rs`: `Comp`, `Delay` and the five constants. Building a value runs nothing.
- `reference.rs`: the equations of §7.4.2, transcribed literally, plus draft 2's `pfix` rule for comparison.
- `machine.rs`: the stack-safe machine of §7.4.4.
- `runner.rs`: the runner, with ticks counted separately from policies, and a fuel observer used only to measure counts.
- `typed.rs`: the proposal's types on top, so `rustc` plays the elaborator's type checker. Signatures are marker types, a row variable is a generic parameter, and each definition's private recursion signature is a unique type. Whether a program can be *expressed* under the request translation is checked by compiling it.

The review's test table [RV §9], as run (`cargo test -p stitchwort-partial-model`):

| Test | Result |
|---|---|
| Immediate return, one request, two requests | 0, 1, 2 ticks (1, 2, 3 observations). Draft 2's rules give 2, 4, 6 observations, as the review computed |
| Nested non-tail requests | `fib 10`: 176 ticks, one per recursive call; `sumTo` with non-tail requests: one tick per call |
| Collatz 27 | 111 ticks, 112 observations; fuel 111 suffices and 110 doesn't. Draft 2: 224 observations |
| Mutual calls | `even 10`: 10 ticks. Hofstadter's F/M (nested mutual requests): calls − 1 ticks (F 10: 178, M 10: 170, F 15: 606) |
| Recursive callback through a monomorphic helper | Doesn't compile: "expected `D<Empty, u64>`, found `D<Plus<Rec<Countdown>, Empty>, u64>`" (a `compile_fail` doctest; the error was checked to be this one) |
| … through a row-polymorphic helper | Works: `viaHelper 5`, 5 ticks; a callback under a lambda called twice per level (`tree 3`), 14 ticks; callbacks in a record used inside the description, 4 ticks |
| A recursive function returning a closure over itself | Doesn't compile (`compile_fail` doctest, checked: "expected `PFn<Empty, u64, u64>`, found `PFn<Plus<Rec<Retry>, Empty>, u64, u64>`"). Over an already-defined function: works |
| `bindD` callbacks constructing fresh `pfix` values | Works; ticks counted for the fresh function (a `pfix` built inside the continuation, after the outer `Delay`) |
| Suspended states | Building `pfix f x` doesn't run `f`; entering runs the body up to its first request; the callee runs only when the `Later`'s rest is stepped |
| Recursion mixed with operations and mappings | Complete traces compared, ticks included: a tail loop reading and printing; operations before and after non-tail requests stay in order; a recursive function calling another (nested `tie`s); a mapping that turns one signature's operation into `readLine` and translates replies; a mapping that turns an operation *into* a recursion request; a mapping around a whole recursive computation |
| Machine against equations | Identical traces on every program above and on 1,200 generated programs (binds, requests, operations, mappings around requests, nested partial calls) |
| Long chains | A million left-nested binds; non-tail recursion 100,000 deep (frames on the heap: 100,001 at peak); a million-iteration tail loop in 1 frame; 10,000 callbacks each running a bounded observation. All on the default 2 MB test-thread stack |
| A foreign operation that never returns | `step` returns it as a request without calling the host (it has none); a fuel observer returns it as data; only the runner is stuck, and reports it |
| Runner policies | Tick limit (inconclusive), work per step, output cap and cancellation each stop a run, independently of ticks |

**What the model doesn't show.** It is untyped underneath, with Rust's types as a stand-in for the elaborator's; the real elaborator's diagnostics, dependent result types `B x` (the model's `Res` is fixed per definition) and universe levels aren't modelled. Re-entrant bounded observation nests one host frame per *nested* observation; that's a stage-2 concern (§10.1).

### 9.2 Stage 1

- **Kernel:** §7.2.
- **Elaborator:** §7.3: `Partial` as a mode; the request translation for every reference; argument packing; `lift` subsumption with function wrappers; the higher-order restriction and its diagnostics (E-PARTIAL-CALLBACK, E-PARTIAL-ESCAPE, E-PARTIAL-NONUNIFORM); the handler restriction.
- **Run mode and runner:** §7.4 and §7.5, with semantics-preservation tests against the equations (ported from the model) and complete-trace tests of the §4 programs.
- **JS:** §7.6's erasure and export check.
- **Examples:** `adder.sw` loses its fuel; the four programs of §4 become examples; §8's tests.
- **DESIGN.md rules this changes:**
  - rule 4 becomes "`Partial` has no operations; no handler may have it in its residual row";
  - rule 5: tests of partial programs use tick limits, and running out is inconclusive;
  - rule 7 stays.

### 9.3 What stage 1 needs from the mutual-recursion work

The motivating programs `serve`/`respond` and `eval`/`apply` are recursive groups, so stage 1's full value needs function groups and forward references ([`mutual-recursion.md`](mutual-recursion.md), stage 2 of that work). Single self-recursive partial definitions don't. The interactions:

1. **Grouping happens on source, before translation.** Whatever finds the strongly connected components of the reference graph (for forward references) must count every source reference, including bare references and partial applications, since those become requests (§7.3.3). It then classifies each group:
   - **all members `Partial`:** the request translation;
   - **no member `Partial`:** `define_group`, saturation and size-change termination, as that proposal says;
   - **mixed** (a total member and a partial member referring to each other, e.g. a total `mk` returning a closure over a partial `loop` that calls `mk`): **refused in stage 1** with a diagnostic suggesting the user split the cycle. Allowing it would need the total member's references to the partial one to be treated as non-recursive, which is plausible (it can only build a `Delay`) but needs its own argument.
2. **A partial group doesn't reach `define_group` as a recursive group.** It's submitted as ordinary non-recursive declarations, in dependency order:
   - the request sum `A` and the response family `B` (data, and a function by cases on the member);
   - one description over the sum, `groupBody : (i : A) -> Delay (Plus (Rec A) op) … (B i)`;
   - one wrapper per member, `g = \fixed… args -> pfix (groupBody fixed…) (inj_g (pack args))`.
   None of them refers to itself, so the group-admission protocol, SCT and saturation all see nothing recursive.
3. **Saturation.** The mutual-recursion saturation rule (§6.3 there) applies to the *checked core*. After translation a partial group's core has no member references, so it's trivially satisfied. A surviving reference (an elaborator bug) is caught by admission: it would refer to a wrapper that isn't final yet. The translation's own eta-expansion of partial applications (§7.3.3) is deliberately different from that proposal's "no automatic eta-expansion": it `let`-binds the supplied arguments first, so evaluation order is preserved, and termination isn't at stake.
4. **Entry arity.** The translation uses the same definition-entry arity as the saturation rule and SCT, computed once, to decide what's a saturated call, a partial application or a bare reference, and which parameters are fixed.
5. **Signatures.** Members' signatures may refer only to final declarations (§5.3 rule 1 there); the same holds for partial members. Their types say `{Partial}`, which translates to `Delay`.
6. **Failure.** If any generated declaration fails, every member of the source group must be reported failed, matching "failed groups publish nothing" (§5.6 there). Since the wrappers depend on the description, admission already makes them fail; the elaborator must also not publish hashes or cached test results for any of them.
7. **Hashing and caching.** The generated declarations are hashed like any other. A change to one member's body changes the shared description, and so every member's hash, which is the same granularity as a total group.

### 9.4 As built: stage 1

**Kernel** (`crates/core/src/partial.rs`, about 290 lines without comments,
nearly all of it the six expected types; plus about 30 lines in `native.rs`
and `hash.rs`). `Delay`, `now`, `lift`, `bindD`, `mapSig` and `pfix` are
prelude signatures without equations (`crates/elab/src/prelude.sw`, after
`Rec` and `RecRes`). `define_primitive` admits each once, `Delay` first,
after checking by conversion that its declared type is exactly §7.2's
(`E-BUILTIN` otherwise, and the definition is failed). A primitive is final
with no body, so it never unfolds, and an application of one is neutral.
Nothing else changed in the kernel: no `case` (it's not a data type), no
eliminator, positivity refuses a type nested in a `Delay` as any nested
occurrence, termination and admission are unchanged. Primitives are hashed
by name and type.

**Elaborator** (untrusted; `crates/elab/src/effects.rs`, `partial.rs`).
- `Partial` in a row is a mode (`Row::partial`): a partial computation type
  is `Delay ops res t`. Sequencing is `bindD`, a result `now`, an
  operation `lift (Call op Done)`, a partial call from another row `mapSig
  m`, a total computation in a partial row `lift` (after `translate`),
  and a total function where a partial one is expected `\x -> lift (f x)`.
  `Partial` is reserved, and messages print a `Delay` as `{…, Partial} a`.
- **E-PARTIAL** (a code beyond the three named in §7.3): running partial
  code in a total context, including a handled computation (§7.3.8) and a
  partial function for a row variable (§7.3.6).
- **Classification** (§9.3): in a recursive group (the module's SCCs, which
  count every reference), a member is partial if its result is a `Delay`
  once it has the parameters its equations bind. So `mk : Nat -> (Nat ->
  {Partial} Nat)` with `mk n = …` is total (it returns a partial
  function). All partial: translated; none: as before; mixed:
  **E-PARTIAL-MIXED**, with a label per member.
- **Translation** (§7.3, §9.3), for a group `f, g, …`: `f.Request ps`
  (data, one constructor per member holding its packed arguments),
  `f.Response ps` (by cases), `g.recur` for each member (the request, as a
  definition with the member's parameters), `g.description` (the member's
  equations, elaborated with every member's name standing for its
  `.recur`, in the row `{Rec (f.Request ps), ρ}`), `f.body` (by cases on
  the request) and the members themselves, `g ps xs = pfix (f.body ps)
  (g.request xs)`, admitted together with one `define_group`. Every
  reference (saturated, partial, bare, under a lambda, a sibling) is a use
  of `.recur`, so nothing in the core refers to a member; a partial
  application of `.recur` evaluates its arguments when it's applied, as
  §7.3.3's `let` does. While describing, `Rec (f.Request ps)` is a row label
  (`effects::REC`), so callbacks and `| e` work as in §7.3.4.
- **E-PARTIAL-CALLBACK**: the group's private row reaching a function
  parameter with a fixed row; it names the helper and suggests the
  parameter's type with `| e`. **E-PARTIAL-ESCAPE**: the private row
  reaching a place nothing answers it (returned, stored in returned data).
  **E-PARTIAL-NONUNIFORM**: a call changing a type parameter (found when
  the request rows disagree, and checked again on the descriptions' core
  terms), a large parameter after an ordinary one, members with different
  type parameters or rows, or arguments that can't be packed.
- **Failure**: if any generated declaration fails, the members (still
  pending) are abandoned as failed by the module, so none is hashed or has
  cached tests. Changing one member's body changes `f.body`, and so every
  member's hash.

**Runtime** (`crates/core/src/step.rs`, about 250 lines without comments):
the model's machine (§7.4.4) on evaluator values, with the same frames
(`Bind`, `Map`, `Tie`, `Await`), the same tail-call rule and no host
access: an operation reaching the bottom is returned with a `Pending` step
that the runner resumes with the reply. **Runner** (`crates/driver/src/run.rs`):
`main : () -> {IO, Partial} ()` (a total `main` is lifted); each stretch of
evaluation between two operations or ticks is one budgeted operation; an
optional tick limit (inconclusive) and a trace of events, for tests.
`Session::simulate` of a partial `main` is a scripted run with a limit of
1,000,000 ticks. The playground runs through the same runner, with its
output cap, reads-past-end limit, timeout and Stop.

**JS** (`crates/js`): a call to a definition whose result is a `Delay`,
with all its arguments, is the token `$Delay` (a `Symbol`), without
computing them; with fewer, a function returning it. Such definitions,
descriptions included, are never generated. An export whose type mentions
`Delay` is **E-JS-PARTIAL**; extraction is refused the same way if a
`Delay` constant ever has a body (the pin of §7.6).

**Examples.** `accept/adder.sw` reads until the end of its input
(`addLines total = step total (readLine ()) addLines`, with `step` and
`stepNumber` polymorphic in `| e`); the fuelled version is
`accept/adder-fuel.sw`, whose tests use `simulate`. `accept/cat.sw`,
`accept/collatz.sw` and `accept/partial.sw` (Collatz, a search, Fibonacci,
even/odd, Hofstadter's F/M, callbacks through row-polymorphic helpers,
under lambdas, in a record, a partial application of a member, `mapP` with
total and partial callbacks, a handler whose clause runs partial code,
partial functions mentioned and stored by total code), `extract/partial.sw`.
Rejected: `reject/partial-callback.sw`, `partial-escape.sw`,
`partial-escape-record.sw`, `partial-nonuniform.sw`, `partial-handled.sw`,
`partial-row-variable.sw` (`simulate` of a partial program),
`export-partial.sw`; soundness: `partial-from-total.sw` (`innocent`),
`partial-empty.sw` (a value of an empty type from a partial function),
`partial-drain.sw`, `partial-mixed-group.sw`, `partial-knot.sw` (the
`pfixBad` shape, refused here as E-PARTIAL; the kernel refuses the core
version by termination), `partial-unfold.sw` (`rfl` across `pfix`,
E-REFL) and `partial-nested.sw` (E-POSITIVITY).

**Tests.**
- `crates/driver/tests/partial.rs` compares the runner with the model on
  the model's own programs (`crates/partial-model/tests/programs`), written
  again in Stitchwort: complete traces (operations, replies, ticks)
  identical, and the model's machine identical to its equations on each.
  Ticks, runner and model alike: `immediate 7` 0, `countdown 1`/`2`/`1000`
  1/2/1000, `collatzSteps 1` 0, `collatzSteps 27` 111, `fib 10` 176,
  `sumTo 100` 100, `isEven 10` 10, `isOdd 7` 7, `hofF 10` 178, `hofM 10`
  170, `hofF 15` 606, `viaHelper 5` 5, `tree 3` 14, `stored 4` 4, a fresh
  `pfix` in a continuation 6; with input and output, `echo` (two inputs),
  `nest 3`, `outer 3` and `sumAsks 3` (an ability handled into `IO`
  between requests); `forever` and `spin` stop at a 50-tick limit, as the
  model's do. Also: a step returns `readLine` and `print` unperformed;
  building `spin 0` runs nothing and its loop keeps constant frames;
  `sumTo 100000` (non-tail, frames on the heap); per-step budgets (20,000
  ticks within a 20,000-step budget; one long total step out of resources
  with no tick); `simulate` of a partial `main`; the adder over 5000 lines,
  agreeing with the fuelled version within its bound.
- `crates/driver/tests/partial_kernel.rs`: the constants are final, opaque
  and hashed; a prelude whose `now` extracts from a `Delay`, whose `pfix`
  keeps the request row, or whose `Delay` is a `Prop`, is E-BUILTIN; each
  is admitted once; a match on a `Delay` is refused (a match on `Nat`, the
  neighbour, isn't); a description running its own wrapper is
  E-TERMINATION (requesting it is accepted); one running an unfinished
  wrapper is E-MALFORMED; conversion never unfolds `pfix`.
- `crates/cli/tests/run.rs`: `stitchwort run` of the adder over 5000
  lines, cat, collatz, and an endless `main` still running after two
  seconds (then killed). `crates/web`: cat and an endless printer stopped
  by the output cap; the browser tests pass.

**Mutation evidence** (each applied by hand, run, reverted):
- *A total context may run partial code* (the `E-PARTIAL` check in
  `effects::lift` disabled): the examples still don't check, but for the
  wrong reason: `soundness/partial-drain.sw was rejected, but not with
  E-PARTIAL: … expected `{} Empty`, but this has type `{Partial} Empty``,
  and the same for `reject/partial-handled.sw`. The kernel refuses the
  ill-typed core (a `Delay` where a `Comp` is expected), which is §7.9's
  "a total type is a `Comp` type".
- *`step` performs host requests itself* (answering `readLine` with end of
  input and `print` with `()` inside the step): 7 of 9 tests in
  `partial.rs` fail, e.g. `echo 0 with input ["a", "", "b c"]: left: [],
  right: [Read(Some("a")), Print("a"), Tick, …]`, and
  `a_step_returns_operations_without_performing_them`.
- *No mixed-group refusal* (mixed groups checked as total):
  `soundness/partial-mixed-group.sw was rejected, but not with
  E-PARTIAL-MIXED: … `loop` takes 1 argument; it's given none here` (the
  termination checker's saturation rule refuses it instead).
- *Members' names left referring to the members while describing*: every
  partial recursive example is refused by admission, `E-MALFORMED … this
  refers to `collatzSteps`, which isn't finished`: a surviving reference
  can't get past the kernel (§7.3.7).

**Benchmarks.** Counts are unchanged except `run-prints`, whose peak heap
went from 6 kB to 8 kB (steps +0.1%): every `main` is now stepped as a
`Delay`.

**Where this differs from the draft.**
- *Fixed parameters* (§7.3.5) are the leading large parameters (types,
  type families, rows), which every call must pass on unchanged. An
  ordinary parameter that every call passes unchanged (`firstFrom`'s `p`)
  is packed into the request rather than shared: the same results and
  ticks. A large parameter after an ordinary one is refused, as are group
  members with different type parameters or rows.
- *Classification* is at the entry arity, so a function returning partial
  functions is total, and in a cycle with a partial one is mixed.
- *Requests* are per-member definitions (`.recur`) rather than lambdas
  written in place; partial applications behave the same.
- *Two more codes*: E-PARTIAL and E-PARTIAL-MIXED.
- *`Next`* isn't in the prelude: `step` is the runtime's, in Rust.
- *Hand-written descriptions* at the surface (calling `pfix` with a
  description over `Rec`) are refused with E-PARTIAL: the private row is
  recognised only while translating. So `pfixBad` (§8.3) can't be written
  at the surface at all; in core terms, the kernel refuses it.
- *Budgets*: work per step restarts at every operation as well as every
  tick (as before `Partial`), and the command line has no total-work
  limit: an endless partial `main` runs until it's stopped.

**Not done.** No generated-program differential test against the model
(its 1,200 random programs are compared with its equations, not with the
runner); the model's mapping *into* the recursion signature (`again`) has
no surface counterpart. No `mapP` in the prelude (it's in
`accept/partial.sw`), and E-PARTIAL-CALLBACK doesn't yet point at
polymorphic variants of library functions.

## 10. Someday/maybe

None of these is planned. Each records what it would give, what it would need, and the review's concerns, so a later decision starts from here.

### 10.1 Observing a `Delay` with fuel; partial correctness (draft 2's stage 2)

**What it gives.** Total code could run a partial computation for a bounded number of ticks and get `Maybe` an answer:

```
runFor : Nat -> Delay op res a -> Comp op res (Maybe a)
runFor n d = bind (step d) (afterStep n)

afterStep : Nat -> Next a (Delay op res a) -> Comp op res (Maybe a)
afterStep n        (Now x)    = Done (Just x)
afterStep Zero     (Later d') = Done Nothing
afterStep (Succ n) (Later d') = runFor n d'
```

This is structural on `n` (a mutual pair), with seeing `Now` free (§7.4.3). With it come `withFuel` (DESIGN.md §16, question 10), `simulateFor` for testing partial programs in the language, and two proof forms that need no bisimilarity:
- **convergence:** `∃ n. runFor n d = Done (Just v)`, Capretta's inductive convergence [C1];
- **partial correctness:** `∀ n v. runFor n d = Done (Just v) -> P v`, "if it finishes, it's right", F*'s and `partial_fixpoint`'s notion [F2, L2].

**What it needs.** `step` as a kernel constant with checked computation rules, and a real argument that a total program calling `step` still terminates. Draft 2's argument ("every function invoked by `step` receives only values built before the `pfix` being unfolded") is **not sufficient** [RV §3]: in `bindD (now x) fresh`, where `fresh x = pfix someDescription x`, stepping runs `fresh x` and steps a `Delay` built *during* the step. That's reasonable programming, not a counterexample, but it shows construction order isn't the measure. The model runs exactly this case (§9.1).

**The review's concerns, as requirements.**
- **Replace the construction-order invariant with a productive-observer argument**, in three separate obligations: (1) a semantic model, `Delay` as the final coalgebra of `X ↦ Comp op res (Next a X)` (an M-type; [M1] constructs M-types in a subsystem of HoTT with univalence, which isn't automatically an implementation or normalisation theorem here); (2) that the concrete interpreter reaches the next observation without running queued recursion internally, covering `bindD`, mappings, continuations and nested uses of `step`; (3) that the kernel's reduction rules still normalise under binders and on open terms.
- **Do (2) as a typed abstract-machine specification** with explicit pending continuations and suspension boundaries, related to ITrees' `interp_mrec`/`mrec`, where a recursive request extends the pending computation with the requested body and the continuation [I1]. A logical-relations argument then accounts for user callbacks that construct or observe delayed values. The model's machine (§7.4.4) is a starting point, untyped.
- **Foreign calls are never executed inside a pure step** (§7.4.5). Otherwise `runEmpty (runFor 1 (foreignSpin ()))` hangs with no `Partial` in its type.
- **Decide conversion of `step`.** Either `step` stays neutral in conversion (runtime tests may observe with fuel, but a successful run isn't a kernel-checked `rfl`), or it gets checked reduction rules (bounded results take part in proofs by computation, and productivity, open-term normalisation and quoting internal states such as `tie` back into core terms must all be addressed). The review favours the second as the eventual goal, without any `Delay` eta rule; never let a runtime-only result silently become evidence the kernel accepts.
- **Keep "well-founded" distinct from "finite"** in the argument (§7.4.2).
- **Fuel observations stay exact.** No bisimilarity quotient, so `collatzSteps 1` and a version with an extra tick are different values; "same eventual result" is a separate, explicitly stated relation.
- **Re-entry.** A callback that runs a bounded observation inside a step nests one host frame per nested observation (the model's `run_for`); a real implementation must keep that bounded or on the heap.
- JS erasure (§7.6) stops being valid and must be replaced.

### 10.2 Promoting proven-terminating partial code to total

**What it gives.** Prove a partial function terminates on some domain, then use it as a total function there: McBride's Bove–Capretta construction [C4, §8], or well-founded recursion.

**What it needs.** An *inspectable* description. McBride's descriptions are inductive `General` trees whose requests can be enumerated; stage 1's return an opaque `Delay`. Two routes:
- an inductive-description sublanguage for the simplest partial definitions (body is a `Comp` over `Rec A` plus total operations, with no calls to other partial functions), where requests can be read off and a domain predicate stated [RV §7];
- or, after §10.1, observational reasoning about arbitrary descriptions.

**The review's concern.** Decreasing requests in the description's *own* signature aren't enough when the body invokes other partial computations. `body n = mapSig sigRight (spin ())` makes no requests at all, so "every request decreases" holds vacuously, yet it diverges. A promotion rule must also justify every partial computation the body calls.

### 10.3 Equivalence of partial programs

Proving two partial programs equivalent (weak bisimilarity, "equal up to ticks") is research-level: it's coinductive, its transitivity is subtle [C5, §2], quotienting by it needs choice or quotient inductive-inductive types [C2, C3], and ITrees do it with paco [I1]. Not needed for anything above; fuel-based statements (§10.1) cover the practical cases.

### 10.4 Handlers over `Delay` (draft 2's stage 3)

**What it gives.** `runState`, `toMaybe` and similar around partial code, so §4's server could keep its counts in a `State` ability and the interpreter could use `Abort`.

**What it needs, and the concern.** A generic handler on `Delay` whose clauses see a continuation that leads, past a `Later`, back into the handler can step its own continuation's result: the knot of §8.3 again. ITrees avoid it because `interp`'s handler "maps each event to a computation" and never sees the continuation, while the interpreter manages the continuation and needs an iteration structure in the target monad [I1, RV §8]. So the candidate is `interp`-style handlers (monad morphisms from operations to `Delay`, into a state- or exception-passing carrier), not arbitrary deep handlers. Multi-shot handlers (`allResults`) over partial computations are *unsupported*, not proven impossible.

### 10.5 Productive loops

Should `cat` (a loop that performs an operation before every recursive call) be total? That's the Hancock–Setzer/ooAgda view [T2] and Idris' `InfIO` [D5]. **Keep it `Partial`** [RV §8]: "total" here means "finishes", and changing it to include an execution that never completes would change DESIGN.md §3's promise ("finitely many operations") for no gain in this milestone. Productivity is a useful *separate* property; if wanted, it would be a second annotation, not a weakening of totality.

### 10.6 JavaScript exports of partial functions

A partial export would return a *stepper*: `{ run(maxSteps): { done: true, value } | { done: false } }`, so the host chooses a budget and can yield to the event loop. Needed first:
- a JS runtime implementing `step` natively, with frames on the heap (or Bjarnason-style re-association of left-nested binds [T3]);
- an explicit policy for whether successive `run` calls continue the same computation, and how host requests are serviced (returned to the caller, or performed by a host object) [RV §8];
- `maxSteps` bounds ticks, not work: a single step can still be long, so the stepper also needs a work budget (§7.5);
- replacing the erasure of §7.6 with a real representation, and top-level partial values emitted as unevaluated `Delay` objects, so nothing partial runs when a module loads.

### 10.7 Partiality polymorphism

A function polymorphic in partiality itself, rather than a separate `mapP`: a type-level `Bool` selecting `Comp` or `Delay`, with `bind`/`lift` defined by cases. Koka gets this for free because `div` is just a row label [K2]. The review considered excluding it at first acceptable [RV §8].

## 11. The review's answers

The external review of draft 2 [RV] answered draft 2's questions and raised others. Where this draft stands:

| # | Question or finding | The review's answer | Draft 3 |
|---|---|---|---|
| 1 | Is "every function invoked by `step` receives only values built before the `pfix`" the right stage-2 invariant? | No: `bindD (now x) fresh` steps a `Delay` built during the step. Use three obligations and a typed abstract-machine spec related to `interp_mrec` | Stage 2 is someday/maybe; requirements recorded (§10.1). The model runs the `fresh` case |
| 2 | Should conversion compute `step`? | Stage 1: no. Eventually checked reduction rules, without eta; never let runtime results become kernel evidence | Stage 1: `step` isn't in the kernel at all. Recorded for §10.1 |
| 3 | Exclude `Partial` from row variables at first? | Acceptable; `mapP` is reasonable. But helpers receiving recursive callbacks need a residual row variable | Adopted, as an explicit restriction with diagnostics (§7.3.4, §7.3.6) |
| 4 | Is `interp` enough for stage-3 handlers? | Keeping deep handlers out is prudent; `interp`-style is a sensible next target; call multi-shot "unsupported" | Someday/maybe (§10.4), worded as suggested |
| 5 | Does the group encoding need more than `RecRes`? | `RecRes B` suffices; but `A` must contain all changing arguments, and non-uniform polymorphic recursion needs more | Packing rule adopted; non-uniform recursion out of scope (§7.3.5) |
| 6 | Should `cat` be total? | No; productivity is a separate property | Kept `Partial` (§10.5) |
| 7 | JS: stepper, or not exportable? | A stepper eventually; but stage 1 needs an explicit extraction policy for reachable partial definitions | Erasure, justified by the one-element model; exports mentioning `Partial` refused (§7.6). Stepper is someday/maybe (§10.6) |
| 8 | One tick per call, operations free? | Operations free is defensible; but the equations gave two ticks per call. Fix one, then decide whether `Now` costs fuel | One tick per recursive call, entering free, `Now` free (§7.4.3). Examples recomputed and measured |
| – | The private signature breaks higher-order uses | Require row-polymorphic helpers; translate every reference; test stored and returned callbacks | §7.3.3–§7.3.4; tested in the model |
| – | Strict evaluation makes `Done (Later (tie f (f x)))` ambiguous; `tie`/`resume` underspecified | Explicit suspended states; full specifications preserving ticks | §7.4.1–§7.4.2 |
| – | "Never reaches the termination checker" | Reword: ordinary kernel checking, no exemption | §7.3.7, §8.6 |
| – | Consistency argument | Convincing; qualify that it doesn't establish the interpreter's correctness | §7.8 |
| – | Foreign calls inside `step` | `step` describes host requests, never performs them | §7.4.5, §8.8 |
| – | Fuel vs execution budgets | Separate runner policies | §7.5 |
| – | Proof story overpromises | Narrow it; decreasing own requests isn't enough | §7.7, §10.2 |
| – | `collatzSteps 1 = now 0` "true at runtime" | Say "same eventual result"; keep fuel observations exact | §7.7, §8.5 |
| – | Survey: Agda `NON_TERMINATING` and `--safe`; Idris's guarantees | Incompatible with `--safe`; Idris does check totality | §5.6, §5.12 |
| – | Prototype test table | Six kinds of test, comparing complete traces | All run (§9.1) |

**Where this draft differs from the review, or goes beyond it.**
- **The tick convention** is a choice the review left open. Draft 3 counts recursive calls only (entering is free), not McBride's one `later` per call including the first (§7.4.3). One consequence: under draft 3, `collatzSteps 1` and `now 0` step identically, so the review's remark that they're distinguishable by fuel is true of draft 2's rules but not of these. The wording change ("same eventual result") stands anyway.
- **Automatic eta-expansion of partial applications** inside partial groups (§7.3.3), unlike the mutual-recursion policy for total groups, because building a request is harmless and the supplied arguments are `let`-bound first.
- **No `Self` request** to repair escapes (§7.3.4). The review warned against passing the tied function in; draft 3 also rules out the variant that delivers it by a request, for the same reason.
- **Foreign functions** are host operations only. The review also allowed "a genuinely total/cooperative stepping implementation"; nothing in stage 1 needs that, so it's left out.
- **Mixed total/partial recursive groups** are refused in stage 1 (§9.3), a restriction the review didn't discuss.

## What I couldn't verify

- **No proofs.** The consistency argument (§7.8) is a short model argument that the review checked; the semantics-preservation obligation is met by tests, not proof.
- **The model is a model.** `crates/partial-model` checks the runtime rules, tick counts and the translation's typing boundary with Rust's types standing in for the elaborator's. It doesn't check dependent result types, universes, the real elaborator's diagnostics or the kernel's handling of the new constants.
- **Stage 2's argument** (§10.1) is a list of requirements, not an outline. I haven't checked that the M-type for `X ↦ Comp op res (Next a X)` is constructed by [M1] (abstract only).
- **Read only in abstract or snippets:** Nakano [G1], Atkey and McBride [G2], Bahr, Grathwohl and Møgelberg [G3], Paviotti, Møgelberg and Birkedal [G4], and Veltri and Vezzosi's guarded cubical Agda.
- **Oury's 2008 Coq-Club post** is known only through [C7]'s citation and a mailing-list snippet.
- **ITrees' `interp_mrec`**: described here from the review's reading of the library and from [I1]; I haven't read the current source myself.
- **F\*:** how `Dv` code specifically is extracted, and the full list of effect abbreviations (`GTot`, `Lemma`, `ML`).
- **Lean:**
  - the description of the compiled auxiliary for `partial def` comes from reading `src/Lean/Elab/PreDefinition/*.lean`;
  - the LNCS volume numbers for [C3] and [C4] are from memory.
- **Idris 2:** what the `%unsafe` pragma does to callers of `assert_total`. It isn't documented in the pragma reference.
- **Unison:** no positive statement either way about tracking divergence.
- **Universes:** the claims that the existential `Machine` encoding needs `Type 1`, and that packing a type argument would (§7.3.5), are from the kernel's rules (`docs/core.md`: numbered universes, no cumulativity; `Sig : Type 1` in the prelude). I didn't try them.

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
- [A7] Agda manual, *Safe Agda*. <https://agda.readthedocs.io/en/latest/language/safe-agda.html>
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
- [RV] External review of draft 2 of this proposal, 15 October 2026 (not in the repository). Section numbers refer to the review's own sections.

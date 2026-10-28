# Computations as values: a survey for D1141

**Decided (Matt, 24 Oct 2026): D1141 (d)** — arrows only, plus erased proof-only reification, following the [external review](computation-values-external-review.md), not this note's recommendation (b).

Status: research note, 24 Oct 2026. No compiler changes. It informs
**D1141**: whether a computation type such as `{Fail} Range` may be written
as an input type (parameters, `let`, fields: "anywhere a type is written"),
only in binder and `let` annotations, or not at all (Unison-style thunks
`() -> {Fail} Range` instead). D1141 is the decision written up as D1134 in
"As built (stage 1, first part)" of [effect-polymorphism.md](effect-polymorphism.md)
on the stage 1 branch (`f111cbe4`). The related D1140 (a) is that an operand
of `=` and the branches of an `if` or `match` whose expected type is a
computation are passed as written, not run.

How claims are marked:

- **[checked]**: read in Stitchwort's source on `main` at `fe12e534`, or on
  the stage 1 branch at `f111cbe4`, with `file:line`.
- **[inferred]**: my reading, not tested.
- **[unverified]**: about another system, and I couldn't find a source that
  says it.
- Every other claim about another language or paper gives the URL and
  section I read, usually with a short quote.

## 1. The question in one page

In Stitchwort an effectful computation is data. The elaborator turns
`{Fail} b` into a tree type, `Comp ops res b`, with `Done x` (finished with
`x`) and `Call op k` (asks for operation `op`, then continues with `k`)
(`crates/elab/src/std/core/Effect.sw:12`) **[checked]**. Since stage 1, a
bare row `{e} b` is `CompIn e b`, which *is* `b` when `e` is the empty row
("As built (stage 1, first part)", `f111cbe4`) **[checked]**.

Programs write `{…}` only after an arrow, as a function's result type
(`parser.rs:1933-1941`, `result_type`) **[checked]**. In a body, a
computation used where a plain value is expected runs there (D1055), and since
stage 0 one passed where a computation is expected is passed as it is
(`docs/syntax.md:604`) **[checked]**.

A proof needs more than that. `Fail.toResultMapIn`
(`docs/proposals/errors.md:331`) is proved by induction on the list, and its
step needs a lemma whose *input* is a `{Fail}` computation, split on
whether that computation fails:

```
-- wanted (sketch; not valid Stitchwort today)
theorem Fail.toResultThen (c: {Fail} a) (k: a -> {Fail} b):
    Fail.toResult (() => k c) =
      (match Fail.toResult (() => c) with
        | Ok x => Fail.toResult (() => k x)
        | Err m => Err m)
  -- by cases on c: Done x => rfl; a failing Call => rfl
```

Today `(c: {Fail} a)` is a parse error, and the ability's result function
has no source name, so the type can't be spelled out by hand either ("As
built (stage 0)", "`Fail.toResultMapIn` isn't built") **[checked]**. D1141
is about how far to open that door.

## 2. Terms used

- **Direct style.** Effectful code is written like ordinary code
  (`let n := need o`), with no `bind` or `do`. Unison, Koka, Frank, Effekt and
  Stitchwort's surface work this way.
- **Monadic style.** A computation is a value of a type like `m a` and is
  sequenced explicitly (`>>=`, `do`). Haskell, Lean and Idris work this way.
- **Thunk** (delayed or suspended computation). A function with no real
  argument, `() -> {E} a`, which runs when it is called (forced).
- **Value type and computation type.** Levy's call-by-push-value separates
  them: "a value is, whereas a computation does", and "an identifier in CBPV
  can be bound only to a value, so it must have value type" (Levy, HOSC 2006
  preprint, §3, [hosc05.pdf](https://www.cs.bham.ac.uk/~pbl/papers/hosc05.pdf)).
  A computation becomes a value only as a thunk, of type `U B`, and is run by
  `force`.
- **Inspect.** Code (or a proof) looks at *how* a computation is built
  (finished, or asking for an operation), rather than only running it or
  handing it to a handler.

## 3. Direct-style languages

### Unison

- **Computation as value:** only as a thunk. "An expression can appear
  delayed as `do e` or `'e`, which are both the same as `_ -> e` and `() ->
  e`." Its type is written `'{IO, Exception} ()`. It is forced with `c()` or
  `!c` ([language reference, "Delayed computations"](https://www.unison-lang.org/docs/language-reference/delayed-computations/)).
- **Where `{A} T` appears:** "The general form for a function type in Unison
  is `I ->{A} O`" ([reference, "Abilities in function types"](https://unison-lang.org/docs/language-reference/abilities-in-function-types)).
  The FAQ: "Think of the ability constraint as a constraint on the function
  arrow as opposed to a constraint on a value"; and "Currently values at the
  'top level' of a program have to be pure"
  ([abilities FAQ](https://www.unison-lang.org/docs/fundamentals/abilities/faqs/)).
  `{A} T` appears in the reference only as the type of an expression being
  handled: "if `e` has type `{A} T` and `h` has type `Request A T -> R`, then
  `handle e with h` has type `R`"
  ([reference, "Abilities and ability handlers"](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/)).
  Whether `x: {Abort} Nat` is accepted as a parameter type: **[unverified]**.
  No page I read says either way, and the types grammar has no
  standalone ability-annotated type.
- **Inspection:** a thunk can only be called. But a handler receives a
  `Request {A} r` value, one step of the computation (an operation and its
  continuation, or the finished value `{ x }`), and matches on it (same
  reference page). So Unison exposes one step at a time, to handlers only.
- **Proofs:** none (Unison has no prover).

### Koka

- **Computation as value:** only as a function, `() -> e a`. "An
  expression between braces (ah, suspenders!) is suspended" (Koka book §3.1.4,
  [book](https://koka-lang.github.io/koka/doc/book.html)).
- **Where effects appear:** only after a function arrow. The grammar is
  `tarrow ::= tatom [ -> tresult ]`, `tresult ::= tatom [ tbasic ]` (book
  §4.4.13). Leijen's paper gives the reason: "an expression with type int can
  really be modeled semantically as an integer (and not as a delayed
  computation …). As a consequence, the only point where side effects can
  occur is during function application" (Leijen, MSFP 2014, §2.1,
  [arXiv 1406.2061](https://arxiv.org/pdf/1406.2061)).
- **Inspection:** none found; functions are called or handled
  **[unverified]** as an explicit statement.
- **Reasoning:** types have a mathematical reading, e.g.
  "〚int -> exn int〛 = ℤ → (ℤ + 1)", which "enables effective equational
  reasoning" (book §3.2.1). No prover.

### Frank

Frank is the closest direct-style precedent, because it *does* have a value
type for computations, written with braces.

- **Computation as value:** yes. "Computations, such as functions, have
  computation types, which embed explicitly into the value types: braces play
  the role of 'suspenders' in types and values." "A value type A is a data
  type D R1 ... Rn, a suspended computation type {C}, or a type variable X"
  (Lindley, McBride, McLaughlin, "Do Be Do Be Do", POPL 2017, §2.2,
  [arXiv 1611.09259](https://arxiv.org/abs/1611.09259)). The type system is
  "inspired by Levy's call-by-push-value" (§2).
- **Where:** anywhere a value type goes, including arguments
  (`if : Bool -> {X} -> {X} -> X`, §2.3) and data fields: §6, "Computations
  as Data", stores them in `data Log [ε] X = start {[ε]X} | inched (Log [ε] X)
  {Char -> [ε]X} | …`, saying the type system admits data types "exactly to
  facilitate the storage of suspended computations".
- **Running:** explicit. "t and f are not values of type X. Rather, they are
  suspended computations of type {X} … The postfix ! denotes nullary
  application of a suspended computation" (§2.3).
- **Inspection:** no. "Frank computations are abstract: a thing of type {C}
  can be communicated or invoked, but not inspected." The paper contrasts
  this with free monads: "we could implement operators like state, pipe and
  catch as abstractions over computations reified as command-response trees.
  By contrast, our handlers do not abstract over computations" (§2.9). An
  argument arriving at a handler's port can be matched one request at a time
  (`<send x -> s>`, §2.6–2.7), as in Unison.
- **Handlers:** "handling by application": a handler is a function whose
  arguments are computations, so there's no separate `handle` syntax (§2.6).

### Effekt

- **Computation as value:** only when boxed. "Following Paul Levy's
  Call-By-Push-Value, Effekt distinguishes between values … and
  computations." "Functions (and all other computation types) are
  second-class in Effekt." "On the term-level, `box`ing offers a way of
  transforming a second-class computation into a first-class value"
  ([tour, "Computations"](https://effekt-lang.org/tour/computation)).
- **Where:** a block (computation) can be passed as an argument but not
  returned or stored: "blocks are considered second-class and can neither be
  returned nor stored in data structures" (Brachthäuser, Schuster,
  Ostermann, "Effects as capabilities", OOPSLA 2020, tech report §1.6,
  [PDF](https://se.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf)).
  A boxed block `σ at C` is a value type and goes anywhere (Brachthäuser et
  al., OOPSLA 2022, extended version §4.1.4,
  [PDF](https://se.informatik.uni-tuebingen.de/publications/brachthaeuser22effects.pdf)).
- **Why second-class:** effects are capabilities, and a stored block could
  outlive the handler it uses: "effect operations only take expressions as
  arguments and never blocks. Otherwise blocks could escape their scope"
  (2020, §3). Boxing lifts the restriction "at the cost of needing to track
  degree-of-impurity information in types" (2022, abstract).
- **Inspection:** none found **[unverified]**.

### Eff, Links, Helium, Flix, OCaml 5

All keep effects on the arrow; a computation as a value is a thunk.

- **Eff.** Core Eff's types "consist of pure types for expressions and dirty
  types for computations", `A ! Δ`; "the function type takes pure types to
  dirty ones" (Bauer and Pretnar, "An effect system for algebraic effects and
  handlers", LMCS 2014, §2, [arXiv 1306.6316](https://arxiv.org/pdf/1306.6316)).
  The earlier language had no effect types at all: "Types in eff … do not
  capture any information about computational effects" (2012, §3,
  [arXiv 1203.1539](https://arxiv.org/abs/1203.1539)).
- **Links.** "Links employs a strict evaluation strategy, so we thunk
  computations that we wish to handle", with
  `typename Comp(e::Row,a) = () { |e}~> a;`. Handlers take these as
  arguments. And: "as with most other implementations of effect handlers, we
  do not consider equations" (Hillerström and Lindley, TyDe 2016, §2,
  [PDF](https://homepages.inf.ed.ac.uk/slindley/papers/links-effect.pdf)).
- **Helium.** `val withUF : (Unit ->[UF a | r] b) ->[|r] b`: a thunk passed
  to a handler function (Biernacki et al., POPL 2019, §1–2,
  [PDF](https://ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf)).
- **Flix.** `def map(f: a -> b \ ef, l: List[a]): List[b] \ ef`; handlers
  take `Unit -> a \ Throw` ([effect polymorphism](https://doc.flix.dev/effect-polymorphism.html)).
  That effects never appear elsewhere is **[unverified]**.
- **OCaml 5.** Effects are untyped: "the compiler does not statically ensure
  that all the effects performed by the program are handled" (manual
  §24.5, [effects](https://ocaml.org/manual/5.3/effects.html)). A computation
  is a plain function, run by `match_with f v h`
  ([Effect.Deep](https://ocaml.org/manual/5.3/api/Effect.Deep.html)).

### Scala 3

Two Scala features match the shape of the D1141 options, though neither is an
effect-handler system.

- **By-name parameters** are a delayed type allowed only on parameters: "The
  type of a value parameter may be prefixed by `=>`, e.g. `x: => T`", the
  argument "evaluated at each use within the function"; and "The by-name
  modifier is disallowed for parameters of classes that carry a `val` or
  `var` prefix" (Scala 2.13 spec §4.6.1, "By-Name Parameters",
  [spec](https://scala-lang.org/files/archive/spec/2.13/04-basic-declarations-and-definitions.html)).
  This is option (b)'s shape. The parameter is also used implicitly: naming
  `x` runs it, as Stitchwort's D1055 does.
- **Capture checking** puts capabilities on any type, `T^{c}`, including
  fields and `val`s: `val l: Logger^{fs} = Logger(fs)`, "The capability is
  passed to the Logger constructor and retained as a field"
  ([capture checking reference](https://docs.scala-lang.org/scala3/reference/experimental/cc.html),
  "Function Types"). This is option (a)'s shape, for capabilities.

## 4. Monadic languages and provers

Here the computation is an ordinary value of type `m a`, usable anywhere a
type goes. What differs is whether a proof can look inside it.

### Haskell

- Plain monads: "it is best to think of a monad as an abstract datatype of
  actions", with the three monad laws
  ([Control.Monad](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Control-Monad.html)).
  `m a` goes anywhere: arguments, fields, lists.
- Free and freer monads are data, so code can match on them:
  `data Free f a = Pure a | Free (f (Free f a))`
  ([free](https://hackage.haskell.org/package/free/docs/Control-Monad-Free.html));
  `Impure :: f x → (x → FFree f a) → FFree f a`, and interpreters match:
  `runReader (Pure v) = v` (Kiselyov and Ishii 2015, §2,
  [PDF](https://okmij.org/ftp/Haskell/extensible/more.pdf)). This is
  Stitchwort's `Comp`.
- polysemy and effectful are not inspectable. polysemy's `Sem` is a function
  over an interpreter
  ([Polysemy.Internal](https://hackage.haskell.org/package/polysemy/docs/Polysemy-Internal.html));
  effectful is "essentially a ReaderT over IO"
  ([README](https://github.com/haskell-effectful/effectful)). That neither
  can be matched on is my reading of the definitions **[inferred]**.

### Lean 4

- Computations are values, and core lemmas take them as inputs:
  `theorem run_bind [Monad m] (x : ExceptT ε m α) (f : α → ExceptT ε m β)`,
  whose right side is a `match` on `Except.ok x` / `Except.error e`
  ([Init/Control/Lawful/Instances.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Control/Lawful/Instances.lean),
  line 51). This is the Lean form of the lemma in §1.
- Lemmas about concrete monads are proved by cases on the computation:
  `(bind_assoc := fun a _ _ => by cases a <;> rfl)` for `Except`
  (same file, line 164).
- `List.mapM` has generic lemmas under `LawfulMonad`: `mapM_cons`,
  `mapM_pure`, and `idRun_mapM : (l.mapM f).run = l.map (f · |>.run)`
  ([Init/Data/List/Monadic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/List/Monadic.lean),
  lines 66–73).
- Hoare-style tools: Lean 4.22 added `Std.Do`, "a Hoare logic for monadic
  programs", with `mvcgen` turning "`⦃P⦄ prog ⦃Q⦄` into pure verification
  conditions" ([v4.22.0 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/)).
  The reference now says it is "superseded by `vcgen`", which "works on any
  program type `Prog` that carries a `Std.WP.WP` interpretation", including
  an inductive type of commands
  ([vcgen](https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/)).

### Idris 2

- `App es a` is a value, and handlers take it as an argument:
  `catch : HasErr err es => App es a -> (err -> App es a) -> App es a`
  ([Exceptions and State](https://idris2.readthedocs.io/en/latest/app/exceptionsstate.html)).
- It is a world-passing function, not a tree
  (`MkApp : (1 prog : (1 w : %World) -> …)`,
  [Control/App.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Control/App.idr)),
  so a proof can't split on it. The guarantees come from linear types.

### F\*

- Effectful terms have computation types (`ST a wp`, `Dv t`) and are
  abstract by default. `reify` exposes the representation to proofs:
  "The reify coercion reveals the representation of an ST computation as a
  Pure function", which gives "a means of doing extrinsic proofs by reifying
  stateful programs" (Ahman et al., "Dijkstra monads for free", POPL 2017,
  §2.4, [ar5iv](https://ar5iv.arxiv.org/html/1608.06499)).
- Only for terminating effects: "this extrinsic style only works for
  terminating code" (§1). Divergence is primitive: "One cannot even state
  properties of `Dv` computations in specifications"
  ([F\* book, Div](https://fstar-lang.org/tutorial/book/part4/part4_div.html)).
- Recent work builds an effect on a free-monad tree and reifies it:
  "Reification allows us to reveal the underlying free-monad-based
  representation of these effects in proofs"
  (SecRef\*, [arXiv 2503.00404](https://arxiv.org/html/2503.00404)). This
  is the closest match to Stitchwort: direct-ish effectful code over a tree,
  with proofs looking at the tree.

### Rocq and Agda: trees as data

- **FreeSpec** is Stitchwort's shape exactly: `Inductive impure (i :
  interface) (α : Type) : Type := | local (x : α) | request_then {β} (e : i
  β) (f : β -> impure i α)`. Lemmas take an `impure` value and proceed by
  `induction p` ([FreeSpec](https://github.com/lthms/FreeSpec),
  `theories/Core/Impure.v`, `ImpureFacts.v`).
- **Interaction trees** are a coinductive free monad, "a general-purpose
  data structure", forced with `observe`; equality is a bisimulation
  (`eutt`), and "clients … should reason equationally" (Xia et al., POPL
  2020, [arXiv 1906.00046](https://arxiv.org/abs/1906.00046), §2–3).
- **Agda free monads** (Swierstra and Baanen, ICFP 2019,
  [PDF](https://webspace.science.uu.nl/~swier004/publications/2019-icfp-anne.pdf),
  §2) define meaning by cases on the computation value, and failure is the
  `Fail` split from §1: `mustPT P (Pure y) = P y`,
  `mustPT P (Step Abort _) = ⊥`.

### Granule

Effects are a graded modality on ordinary types, `(Char, Char) <IO>`, so
effectful computations are first-class values; reasoning is through the
grades, not by looking inside (Orchard, Liepelt, Eades, ICFP 2019, §2.1,
§4.2, [PDF](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf)).

## 5. Comparison

"Arrow only" means an effect annotation can be written only on a function's
result.

| System | Computation as a value | Type written | Effect type outside an arrow? | Run by | Inspect structure? | Proofs |
|---|---|---|---|---|---|---|
| Unison | thunk | `'{A} T` = `() ->{A} T` | arrow only; `{A} T` only for a handled expression | `!c`, `c()` | handlers see one `Request` step | none |
| Koka | thunk | `() -> e a` | arrow only (grammar) | call | no **[unverified]** | none |
| Frank | suspended computation | `{[E] X}` | yes: a value type, in arguments and data | `c!` (explicit) | no: "abstract"; handler ports match one request | none |
| Effekt | block (2nd class), or boxed value | `A => B / {E}`, `… at {c}` | blocks: parameters only; boxed: anywhere | call; unbox | no **[unverified]** | none |
| Eff / Links / Helium / Flix | thunk | `unit → A ! Δ`, `() {E}~> a`, … | arrow only | call / `handle` | no | Links: "we do not consider equations" |
| OCaml 5 | function | `unit -> 'a` | effects untyped | call under `match_with` | no | none |
| Scala 3 | by-name param; captured value | `=> T`; `T^{c}` | by-name: parameters only; captures: anywhere | implicit on use; call | no | none |
| Haskell (plain, polysemy, effectful) | value | `m a`, `Sem r a`, `Eff es a` | anywhere | interpreter / `runEff` | no | equational (monad laws) |
| Haskell free / freer | value (data) | `Free f a` | anywhere | interpreter | **yes** (pattern match) | equational, by cases |
| Lean 4 | value | `m α`, `Except ε α` | anywhere | `.run`, by cases | for concrete monads | lemmas take computations; `cases`; `vcgen` |
| Idris 2 | value | `App es a` | anywhere | `run` | no (a function) | linear types |
| F\* | computation type | `ST a wp`, `Dv t` | effectful terms are abstract | — | via `reify` (terminating, reifiable only) | WP types + extrinsic proofs by `reify` |
| Rocq / Agda free monads | value (data) | `impure i α`, `itree E R`, `Free C R a` | anywhere | interpreter | **yes** | lemmas take a computation; cases / induction |
| Stitchwort today | tree (data), or thunk | `{A} T` after `->`; thunks `() -> {A} T` | arrow only (`parser.rs:1933`) | implicitly where a value is expected (D1055) | yes for `Comp` written by hand | lemmas over thunks and handlers |

## 6. What the survey shows

1. **Direct-style languages keep effects on the arrow, for a reason
   Stitchwort doesn't share.** Koka says why: in a call-by-value language a
   value has already been computed, so "the only point where side effects can
   occur is during function application" (§3, Koka). A stored computation
   must therefore be a thunk. In Stitchwort a `{Fail} b` value is a tree,
   which has already stopped at its first operation. Holding it performs
   nothing, because an operation does something only when a handler
   interprets it **[inferred]**, from `Effect.sw:12` and the handler
   translation in `abilities.md`. The tree is already the suspension.
2. **Frank shows a direct-style language with a computation type usable
   anywhere**, with braces in type position. But Frank forces explicitly
   (`!`) and makes computations abstract (§2.9).
3. **Effekt's reason for second-class computations doesn't apply.** Effekt
   restricts blocks so that a capability can't outlive its handler. A
   Stitchwort tree holds no capability; it is data waiting for a handler
   (§3, Effekt).
4. **Every prover in the survey lets a lemma take a computation as an
   input.** Lean's `ExceptT.run_bind`, FreeSpec's `induction p`, Agda's
   `mustPT` and F\*'s `reify` all state facts about a computation value and
   split on its shape. Stitchwort's `Comp` is FreeSpec's `impure`, so the
   lemma in §1 is the standard one.
5. **No surveyed system decides "run or pass" from the expected type
   everywhere.** Scala's by-name parameter is the nearest, and it is
   restricted to parameters. Unison, Frank and Effekt mark forcing in the
   source (`!c`, `c!`, unbox). Stitchwort already decides by expected type
   (D1055 and stage 0), so each new place a computation type can appear is a
   new place where a reader must know the expected type.

## 7. What this means for Stitchwort

### 7.1 The options

**(a) `{A, B | e} T` anywhere a type is written**: binder and `let`
annotations, fields, type arguments (`List ({Fail} b)`), a synonym's right
side.

- For: the most uniform. It matches monadic languages and provers, where
  `m a` is a type like any other, and Frank's `{C}`. The elaborator already
  elaborates `Expr::Effect` wherever a type is checked (`check.rs:655-658`,
  `effects.rs:831`) **[checked]**, so it needs only parser work.
- Against: a parse ambiguity. Types are expressions, and a record literal
  can pun a field (`{ age = 0, name }`) and be a bare argument
  (`AtR { q = …, n = 0 }`) (`docs/syntax.md` "Records") **[checked]**. A row
  with a lone lowercase name is a row variable (`parser.rs:1789-1795`)
  **[checked]**. So in expression position `f {e} b` reads either as `f`
  applied to the type `{e} b` or as `f` applied to the record `{ e }` and
  then `b`. Disambiguating needs a rule based on what follows the `}`, and
  that rule would be new to readers. It also lets computations into generic
  containers and type variables, where stage 0 already found that `id c`
  with `id: a -> a` runs `c` ("As built (stage 0)", "Not changed")
  **[checked]**. A computation inside `List ({Fail} b)` would run or stay
  depending on how each access is typed.

**(b) Only after a `:` in an annotation**: `(c: {Fail} b)`, `[c: …]`,
`let c: {Fail} b := …`, and (if the parser shares the binder code) a
constructor field `(run: {IO} ())`. A record type declaration's field
`{ run: {IO} () }` is also after a `:`. Whether constructor and record fields
come for free in the parser is **[inferred]**, not checked.

- For: enough for `Fail.toResultMapIn`'s lemma (§1) and for handlers that
  take a computation. No ambiguity: after `:` a `{` can't start a record
  literal in a type annotation today, and the parser already refuses a record
  type there ("a record type can't be written here: `{` in a type starts an
  ability row", `parser.rs:1770-1780`) **[checked]**. One rule a reader can
  learn: "a computation type can be written after a colon". Scala's by-name
  parameters show that an annotation-only delayed type works in practice.
- Against: a type argument still can't be a computation type, so
  `List ({Fail} b)` needs a thunk, `List (() -> {Fail} b)`. Less uniform than
  (a).

**(c) No new syntax; thunks only** (Unison, Koka, Links, Effekt).

- For: matches the direct-style languages and Stitchwort's own handlers,
  which already take thunks (`Fail.toResult (prog: () -> {Fail | e} a)`,
  `crates/elab/src/std/Fail/Fail.sw:45`) **[checked]**. Nothing new to
  learn.
- Against: the lemma in §1 can't be written over a thunk as it stands.
  Splitting on `t ()` runs the call ("As built (stage 0)": "`match first ()
  with …` runs the call") **[checked]**. The workaround is a helper whose
  parameter is spelled `Comp` with the ability's types read off a function
  (stage 1 doc, D1134 (c)) **[checked]**: it works but exposes the encoding
  in a public theorem, which is what D1122 keeps rows away from. A cleaner
  form of (c) is an F\*-style `reify`: a std function that gives the tree of
  a thunk. That is option (b)'s type under another name, plus a primitive.
  Every prover in §4 lets a lemma take the computation directly.

### 7.2 Interaction with D1140 (a)

D1140 (a) is what makes (a) or (b) useful. With a binder `c: {Fail} b`, the
statement `Fail.toResult (() => c) = …` and a test like `c = Done x` must
treat `c` as the computation, not run it (in a pure statement, running a
`{Fail}` computation is `E-ABILITY`). The stage 1 note says the same: "(a) of
D1134 needs (a) or (c) of D1133 to be useful" **[checked]**. Under (c),
D1140 (a) matters only for `Comp` types written by hand.

### 7.3 Interaction with stage 1's `CompIn`

- A concrete row, `{Fail} b`, elaborates to a `Comp` over `Fail`'s
  operations. It is data: a proof can split it into `Done` and `Call`.
- A bare row, `(c: {e} b)`, is `CompIn e b`. Its constructors and
  eliminators are internal (D1122), so a program can pass `c`, sequence it, or
  hand it to a handler, but not match on it. At a pure use (`e := Empty`) it is
  just a `b`. Rows stay parametric, which is D1122's goal.
- So matching is possible exactly where the row is concrete. That is where
  `Fail.toResultMapIn` needs it.

### 7.4 How each option supports `Fail.toResultMapIn`

- **(a) or (b), with D1140 (a):** state `Fail.toResultThen` (§1) with
  `(c: {Fail} a)` and prove it by cases on `c`: `Done x` and a failing `Call`
  each reduce by `rfl`. `Fail` never resumes, so no induction and no function
  extensionality ("As built (stage 0)") **[checked]**. Then
  `Fail.toResultMapIn` is induction on the list, using it twice per step.
  Passing `f x` as `c` works by stage 0's rule (an argument whose parameter is
  a computation type isn't run) **[checked]**. What the `Call` pattern looks
  like in source (naming the injection into the row's sum of operations) is
  **[unverified]**; see open question 2.
- **(c):** the same proof with a helper typed through the encoding, or with a
  new `reify` primitive.

### 7.5 Handler writing

Under (a) or (b) a handler could take the computation itself, as Frank and
Idris 2 handlers do (`catch : … App es a -> …`):

```
-- sketch, not proposed for std here
def Fail.toResultOf (c: {Fail | e} a): {e} Result a Text :=
  handle c with
    | return x => Ok x
    | Fail.stop msg, k => Err msg
```

and a caller would write `toResultOf (turn t)` with no `() =>`, because stage
0 passes an argument whose parameter is a computation type without running
it. Whether `handle c with` accepts a variable today is **[unverified]**.
`handle` elaborates its body in computation mode (`effects.rs:1605-1614`)
**[checked]**, and a bare variable of `Comp` type is run in place there
(probe 8) **[checked]**, so it probably works **[inferred]**. Whether std
should move from thunk handlers to computation handlers is a separate
question (open question 3). D1141 only makes it possible.

### 7.6 Recommendation: (b)

Allow a computation type after `:` in annotations (binders, `let`, and
fields where the parser treats them as binders). Keep type arguments and
synonyms for later. Together with D1140 (a). The reasons:

1. **The proof needs it, and the provers agree.** Every prover surveyed
   states lemmas about computation values. Stitchwort's representation is
   FreeSpec's, where this is routine (§4). Option (c) works only by exposing
   the encoding or adding a `reify`.
2. **The direct-style objection doesn't transfer.** Koka and Unison keep
   effects on arrows because a call-by-value value has already been computed.
   A Stitchwort tree has already stopped at its first operation and performs
   nothing until handled (§6, point 1). Effekt's capability-escape reason
   doesn't apply either (§6, point 3).
3. **(b) is enough and unambiguous.** It covers the lemma, handlers that
   take computations, and storing a computation in a field. It avoids the
   `f {e} b` ambiguity that (a) brings.
4. **It keeps the run-or-pass rule local.** Stitchwort already decides "run
   or pass" by the expected type, which no surveyed language does everywhere
   (§6, point 5). Under (b) a computation-typed name always has a written
   annotation nearby. Under (a) it can come from a type variable deep in a
   generic container.
5. **Widening later is cheap.** Moving from (b) to (a) only accepts more
   programs, so no existing program changes. If a program needs
   `List ({Fail} b)`, that is the trigger to revisit.

### 7.7 The strongest counter-argument

Every direct-style effect language surveyed either keeps computation types
off value positions (Unison, Koka, Links, Eff, Flix) or allows them only with
explicit forcing and no inspection (Frank's `!` and "abstract"; Effekt's
box and unbox). Stitchwort with (b) would have values that are run *or*
passed depending on the expected type, and that programs can take apart.
Two costs follow:

- **Readability.** A reader can't tell from `c` alone whether it runs.
  Frank and Unison make the reader's job easy with `!`.
- **Runtime freedom.** Once a program can match on a `{Fail} b` value, the
  runtime has to be able to produce the tree. Stage 4 (design F) lists
  evidence passing as a candidate representation
  (`docs/proposals/effect-polymorphism.md:84-87`) **[checked]**, and with it
  the runtime builds no trees. F\* meets the same tension by allowing
  `reify` only for "reifiable" effects.

The answers are partial. On readability, the annotation is always written
nearby under (b), and stage 0 already made the same choice for parameters.
On runtime freedom, handlers are folds over the same trees (`foldComp`,
`Effect.sw:19`) **[checked]**, so the semantics already commits to trees;
only the runtime would need a reify step where a program (not a proof)
matches on a computation. Open question 1 offers a way to limit this.

## 8. Open questions

1. **Matching in programs, or only in proofs?** If matching on a computation
   value (`Done` / `Call`) were allowed only in theorems, as F\* uses
   `reify` for proofs, the stage 4 runtime would keep its freedom. Is that
   worth a rule?
2. **What a `Call` case looks like in source.** Splitting `c: {Fail} a`
   needs a pattern for "`Fail.stop m` was asked for", which today is a `Call`
   of an injection into the row's sum of operations. A std eliminator (say
   `Fail.cases c (onDone) (onFail)`, or a theorem `Fail.doneOrFails c`) may be
   better than exposing the injection. To be settled in the follow-on lane.
3. **Thunk handlers or computation handlers in std?** Under (b),
   `Fail.toResult (turn t)` without `() =>` becomes possible (Frank's
   "handling by application"). Changing std's handlers is a separate decision.
   It would change every caller, and two styles side by side is worse than
   either.
4. **Explicit forcing?** Unison's `!c` and Frank's `c!` make running
   visible. Stitchwort chose implicit running (D1055). Should a stored
   computation (a field, a `let` with a computation annotation) also be
   implicit? This survey doesn't settle it. The current rule is consistent.
5. **`Partial`.** `Delay` isn't a `Comp` for stage 0's rule ("As built
   (stage 0)", "Not changed") **[checked]**. Whether `(c: {Partial} a)`
   should be a binder type too is open. F\*'s divergence caveat (no reify for
   `Dv`) suggests caution.

## Sources read

Unison: [delayed computations](https://www.unison-lang.org/docs/language-reference/delayed-computations/),
[abilities in function types](https://unison-lang.org/docs/language-reference/abilities-in-function-types),
[abilities and ability handlers](https://www.unison-lang.org/docs/language-reference/abilities-and-ability-handlers/),
[abilities FAQ](https://www.unison-lang.org/docs/fundamentals/abilities/faqs/),
[types](https://unison-lang.org/docs/language-reference/types).
Frank: [arXiv 1611.09259](https://arxiv.org/abs/1611.09259) (full text).
CBPV: [Levy, HOSC 2006 preprint](https://www.cs.bham.ac.uk/~pbl/papers/hosc05.pdf).
Koka: [book](https://koka-lang.github.io/koka/doc/book.html),
[Leijen 2014](https://arxiv.org/pdf/1406.2061).
Effekt: [tour: computation](https://effekt-lang.org/tour/computation),
[tour: captures](https://effekt-lang.org/tour/captures),
[OOPSLA 2020 report](https://se.informatik.uni-tuebingen.de/publications/brachthaeuser20effekt.pdf),
[OOPSLA 2022 extended](https://se.informatik.uni-tuebingen.de/publications/brachthaeuser22effects.pdf).
Scala: [2.13 spec §4.6.1](https://scala-lang.org/files/archive/spec/2.13/04-basic-declarations-and-definitions.html),
[capture checking](https://docs.scala-lang.org/scala3/reference/experimental/cc.html).
Eff: [arXiv 1203.1539](https://arxiv.org/abs/1203.1539),
[arXiv 1306.6316](https://arxiv.org/pdf/1306.6316).
Links: [TyDe 2016](https://homepages.inf.ed.ac.uk/slindley/papers/links-effect.pdf).
Helium: [POPL 2019](https://ii.uni.wroc.pl/~ppolesiuk/papers/popl19.pdf).
Flix: [effect polymorphism](https://doc.flix.dev/effect-polymorphism.html).
OCaml: [effects](https://ocaml.org/manual/5.3/effects.html),
[Effect.Deep](https://ocaml.org/manual/5.3/api/Effect.Deep.html).
Haskell: [Control.Monad](https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Control-Monad.html),
[free](https://hackage.haskell.org/package/free/docs/Control-Monad-Free.html),
[freer](https://okmij.org/ftp/Haskell/extensible/more.pdf),
[polysemy](https://hackage.haskell.org/package/polysemy/docs/Polysemy-Internal.html),
[effectful](https://github.com/haskell-effectful/effectful).
Lean: [Lawful/Instances.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Control/Lawful/Instances.lean),
[List/Monadic.lean](https://raw.githubusercontent.com/leanprover/lean4/master/src/Init/Data/List/Monadic.lean),
[v4.22.0 notes](https://lean-lang.org/doc/reference/latest/releases/v4.22.0/),
[vcgen](https://lean-lang.org/doc/reference/latest/The--vcgen--tactic/).
Idris 2: [App](https://idris2.readthedocs.io/en/latest/app/exceptionsstate.html),
[Control/App.idr](https://raw.githubusercontent.com/idris-lang/Idris2/main/libs/base/Control/App.idr).
F\*: [DM4F](https://ar5iv.arxiv.org/html/1608.06499),
[book: Div](https://fstar-lang.org/tutorial/book/part4/part4_div.html),
[SecRef\*](https://arxiv.org/html/2503.00404).
Rocq/Agda: [FreeSpec](https://github.com/lthms/FreeSpec),
[ITrees](https://arxiv.org/abs/1906.00046),
[Swierstra and Baanen](https://webspace.science.uu.nl/~swier004/publications/2019-icfp-anne.pdf).
Granule: [ICFP 2019](https://www.cs.kent.ac.uk/people/staff/dao7/publ/granule-icfp19.pdf).

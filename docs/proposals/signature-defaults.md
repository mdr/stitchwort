# Default values for function parameters

Status: accepted (D1340). Decisions D1345 to D1356 in §10 all taken as recommended (26 Oct 2026).
Nothing here is built.

This note takes up the part of
[named-arguments.md](named-arguments.md) that was put off: §5.4,
"defaults in signatures". D1097 put defaults on record and constructor
fields only (SW-401, SW-402), and said signature defaults would be decided
again once field defaults were in use. Today a parameter with a default is
`E-PARSE`, "a parameter can't have a default value", with a note to use a
record (`crates/syntax/src/parser/declarations.rs:514-520`,
`docs/syntax.md:339`) **[checked]**.

Claims about the codebase cite `file:line` and are marked **[checked]**
(read in the source at `main`, `ffb6ef5f`, 26 Oct 2026) or **[inferred]**.
Claims about other languages cite a primary source that was read; quotes
are verbatim.

## 1. Why now

A program's tests build values with factories like this one:

```
def booking (id: Text) (start: Float) (duration: Float): Booking :=
  { id = { value = id }, start, duration, room = None, guests = [], notes = None }
```

Each test passes every value, though most tests care about one or two.
Matt: "This sort of factory is best spelled `makeBooking` and you can use
named/default arguments to give it useful default values (like None, []),
and tests ideally specify just data that are pertinent to the scenario
rather than every last dot and tittle." The call wanted is:

```
makeBooking "a" (duration := 30.0)
```

Field defaults (`named-arguments.md` §5.1) don't fit this, for two
reasons:

- **The defaults belong to the factory, not the type.** `Booking` is a
  domain type. Production code should give every field: a default of `None`
  for `notes` on the type itself would let production code leave it
  out by accident. The test file wants its own defaults, and different
  test files may want different ones.
- **A factory does more than fill fields.** It wraps (`{ value = id }`),
  derives (an end time from start and duration) and names things the way the
  scenario talks about them. An options record for the factory would be a
  second type mirroring `Booking`, written only to carry defaults.

So the question is how to add `(duration: Float := 60.0)` to a `def`'s
header without the problems §5.4 worried about: defaults fighting currying,
and defaults lost through function values.

## 2. What exists to build on

- **Named arguments** (`named-arguments.md` §4, built): `(x := e)` names an
  explicit parameter, in any order, mixed with positional arguments;
  positional arguments take the first explicit parameter still free
  (D1112); a call that leaves out an explicit parameter before the last one
  it gives is a function of the ones left out, which are rigid variables,
  never inferred (D1095); the names come from the head's declared signature,
  found syntactically (D1115). The call elaborates to the positional term
  (`crates/elab/src/named.rs:1-13`) **[checked]**.
- **Field defaults** (built): each default is a generated helper definition
  taking the type's parameters and the earlier fields it needs, elaborated
  once at the declaration in the empty row, so it is pure and terminates; a
  literal that leaves a field out calls the helper; the helper is kept as
  metadata of the declaration (`Data::defaults`), not in the type's hash
  (`crates/elab/src/defaults.rs:1-30`, `:104-234`;
  `crates/core/src/globals.rs:160-166`) **[checked]**.
- **Run order** (`named-arguments.md` §4.5): effectful arguments run once,
  where written, before the call's stages; a stage reached after a left-out
  parameter runs inside the function the call makes.
- **Local definitions** are written as top-level ones and lifted to
  `owner.name` (`docs/syntax.md:187-209`) **[checked]**. Lambdas take typed
  parameters `(x: Nat) => …` (`docs/syntax.md:169`) **[checked]**.
- **Exports** are uncurried at the JS boundary, with the binder names as the
  TypeScript parameter names, and records with defaulted fields get an input
  shape whose decoder runs the defaults (D1101, D1114; `docs/syntax.md:341-349`)
  **[checked]**.

## 3. Other languages

Each row was read in the source linked.

| Language | Where defaults go | When a default is used | Function values | Notes |
|---|---|---|---|---|
| Scala | `(p: T = expr)` on method parameters | A call that omits the parameter. "To use a default argument, the corresponding parameter has to be omitted in the method application"; a skipped earlier one needs later ones named. | `f _` doesn't use defaults: with `def f(a: Int, b: Boolean = true)`, `f: (Int => Int)` and `(f _): (Int => Int)` are type mismatches ("found: (Int, Boolean) => Int"), while `f(_)` works. A maintainer: "`f(_)` is an application, `f _` is not, so I don't find it especially surprising that default arguments kick in for the former but not the latter." | "For every parameter with a default argument, a synthetic method which computes the default expression is generated", named with "”$default$” and a number indicating the parameter position"; `f(b = "3")` becomes `f(b = "3", a = f$default$1)`. "expr is evaluated every time a method application uses the default argument." A default may use parameters of *earlier parameter lists*, "not on other parameters in the same parameter list"; the getter takes "the value parameter sections preceding the corresponding parameter". Overriding methods inherit defaults and may change them; the runtime receiver's default is used. "At most one overloaded alternative may specify defaults." Not optional from Java. Default parameters are listed among "a common source of binary compatibility breakages". |
| Kotlin | `(x: Int = 0)` | A call without that argument. "default values are only evaluated when the function is called without the corresponding parameter". A defaulted parameter before a required one "can only use the default value by naming the argument". | Since 1.4 a callable reference is adapted when the expected type has fewer parameters: with `fun foo(i: Int = 0): String` and `fun apply(func: () -> String)`, `apply(::foo)` works, and "If the callable reference to the function `foo` takes no arguments, the default value `0` is used". Without such an expected type a reference has the function's full arity: for a value reference its type is "`(Arg0 ... ArgN) -> R`, where `Arg0, ... , ArgN` are … the types of function formal parameters". Reflection's `KCallable.callBy` can omit optional parameters: "Parameter can be omitted from the mapping if it is either optional … or vararg". | "Parameters that refer to the values of other parameters must be declared later in the order." Overrides "always use the base method's default parameter values" and may not declare their own. Java sees "only a full signature" unless `@JvmOverloads` generates one overload per defaulted parameter. |
| OCaml | `?(step = 1)` optional labelled parameters | "If a non-labeled argument is passed, and its corresponding parameter is preceded by one or several optional parameters, then these parameters are defaulted". "All other missing parameters … will be kept". So "you will only be able to eliminate optional arguments by totally applying the function", and "A function taking some optional arguments must also take at least one non-optional argument." | Passed where a function type without them is expected, "the compiler will attempt to transform the argument … by passing None for all optional parameters". | Labels are in the type. Warning 16 is "Unerasable optional argument"; warning 48 "Implicit elimination of optional arguments". When the default is evaluated is "unspecified". |
| Lean 4 | `(x : α := v)`, sugar for `x : optParam α v`, a reducible identity on types; `(h : p := by tac)` is `autoParam` | In the elaborator, when no positional argument is left for an explicit parameter, an `optParam` gets its default and an `autoParam` runs its tactic, unless the application is in explicit mode (`@f`). | A bare `f` is an application with no arguments, so its defaults are filled. A required parameter left over while later ones still have defaults becomes a lambda: "using eta arg since there are still optParams or autoParams". | The default lives in the type, so a parameter of type `(x : Nat := 1) → Nat` keeps it. "Optional and automatic parameters are not part of Lean's core type theory." Positional arguments fill optional parameters too. |
| Idris 2 | `{default 0 lag : Nat}`, implicit parameters only | When the implicit isn't given | — | "primarily intended to assist in automatically constructing a proof where auto fails"; the Fibonacci example "is not the intended use". |
| Swift | `(x: Int = 42)` | "The given expression is evaluated when the function is called. If the parameter is omitted when calling the function, the default value is used instead." | SE-0111 took labels out of function types (see `named-arguments.md` §3). | Style: put parameters without defaults first. For a library, "Default argument expressions for functions that are ABI-public are implicitly `@_alwaysEmitIntoClient`", and "Changing or removing a default argument is a binary-compatible source-breaking change". |
| JavaScript | `(x = 1)` | A missing argument or an explicit `undefined`; "not `null`". "The default argument is evaluated at call time". | `length` stops counting at the first default. | "Parameters defined earlier (to the left) are available to later default parameters". `f(x = 1, y)` is legal: positional arguments still fill left to right. |
| TypeScript | `x?: T`, `x = 10` | As JS. "when a parameter is optional, callers can always pass `undefined`". | A defaulted parameter makes the function's type have an optional parameter. | The handbook's rule for callbacks: "never write an optional parameter unless you intend to call the function without passing that argument". |

Sources:
[Scala SID-1, named and default arguments](https://docs.scala-lang.org/sips/named-and-default-arguments.html);
[Scala 3 specification, expressions](https://scala-lang.org/files/archive/spec/3.4/06-expressions.html);
[Scala 3 eta-expansion](https://docs.scala-lang.org/scala3/reference/changed-features/eta-expansion-spec.html);
[scala/scala3#4275, "Eta-expansion doesn't insert default arguments"](https://github.com/scala/scala3/issues/4275);
[Scala tour, default parameter values](https://docs.scala-lang.org/tour/default-parameter-values.html);
[Scala binary compatibility for library authors](https://docs.scala-lang.org/overviews/core/binary-compatibility-for-library-authors.html);
[Kotlin functions](https://kotlinlang.org/docs/functions.html);
[Kotlin 1.4, callable references with defaults](https://kotlinlang.org/docs/whatsnew14.html);
[Kotlin specification, expressions (callable references)](https://kotlinlang.org/spec/expressions.html);
[Kotlin `KCallable`](https://kotlinlang.org/api/core/kotlin-stdlib/kotlin.reflect/-k-callable/);
[Kotlin, calling Kotlin from Java](https://kotlinlang.org/docs/java-to-kotlin-interop.html);
[OCaml manual, labeled arguments](https://ocaml.org/manual/latest/lablexamples.html);
[OCaml manual, expressions (function application and definition)](https://ocaml.org/manual/latest/expr.html);
[OCaml manual, compiler warnings](https://ocaml.org/manual/latest/comp.html);
[Lean reference, function application](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/);
[Lean source, `optParam` in `Init/Prelude.lean`](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean)
and [`processExplicitArg` in `Lean/Elab/App.lean`](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean);
[Idris 2, miscellany](https://idris2.readthedocs.io/en/latest/tutorial/miscellany.html);
[The Swift Programming Language, functions](https://github.com/swiftlang/swift-book/blob/main/TSPL.docc/LanguageGuide/Functions.md)
and [declarations](https://github.com/swiftlang/swift-book/blob/main/TSPL.docc/ReferenceManual/Declarations.md);
[Swift library evolution](https://github.com/swiftlang/swift/blob/main/docs/LibraryEvolution.rst);
[MDN, default parameters](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/Default_parameters);
[TypeScript handbook, functions](https://www.typescriptlang.org/docs/handbook/2/functions.html).

What this tells us:

1. **Everyone computes the default at each call that uses it**, in the
   caller's call, not once at the declaration (Scala, Kotlin, Swift, JS;
   OCaml leaves it unspecified). Python's "once" is the outlier
   (`named-arguments.md` §3).
2. **Defaults are compiled to something the call site calls** (Scala's
   `f$default$N`, which takes the earlier parameters) or are copied into the
   call site (Swift). Stitchwort's field-default helpers are Scala's design.
3. **Currying is where it goes wrong.** Scala and Kotlin have no curried
   application, so "is the call finished?" never comes up. OCaml has
   currying and needs a rule (a later positional argument finishes the
   optional ones), which leaves a trailing optional parameter that can't be
   dropped. Lean has currying and settles it per written application: the
   arguments written are all there is, so the rest of the defaults are
   filled, and a leftover required parameter becomes a lambda.
4. **Function values lose defaults** in Scala, keep them in the type in Lean
   and TypeScript, and get them filled in Kotlin's references (when the expected
   type has fewer parameters; otherwise a reference has the full arity) and
   OCaml's higher-order use. Stitchwort keeps names, and defaults, out of
   types (`named-arguments.md` §1 non-goals), so Lean's and TypeScript's way
   is closed; Lean's "a bare name fills its defaults" is open. Kotlin's
   adaptation is driven by the expected type, which Stitchwort's checker
   doesn't consult for names (D1115); the written call alone decides
   (D1350).
5. **Positional passing to a defaulted parameter** is allowed everywhere
   except Swift with labels (which forces names for every labelled
   parameter). Kotlin's "a default before a required parameter only works by
   name" is where that rule starts to hurt.

## 4. The design in one page

```
def makeBooking (id: Text)
    (start: Float := 0.0)
    (duration: Float := 60.0)
    (room: Option Text := None)
    (guests: List Guest := [])
    (notes: Option Text := None): Booking :=
  { id = { value = id }, start, duration, room, guests, notes }

test "a short booking is flagged" :=
  let short := makeBooking "a" (duration := 30.0)
  flagged [short] == ["a"]

test "bookings keep their order" :=
  let bookings := ["a", "b", "c"].map makeBooking
  (bookings.map (b => b.id.value)) == ["a", "b", "c"]
```

- **`(x: T := e)` in a `def` or `theorem` header**, top-level or local, on
  an explicit parameter (D1345).
- **A defaulted parameter is given by name only.** Positional arguments
  skip it (D1349). So `makeBooking "a" 0.0` is an error with a fix, and
  adding a default to a function never moves a positional argument.
- **A written call fills every default it doesn't name**, at the end of the
  call, whether or not the call gives every required parameter: a bare
  `makeBooking` is `id => makeBooking id 0.0 60.0 None [] None None None`,
  so `["a", "b"].map makeBooking` works (D1350). Defaults never appear in
  a function value's type (D1352).
- **Each default is a helper definition**, as for fields: checked once at
  the declaration, for every value of the parameters before it; pure; it
  may use those earlier parameters, implicit ones included (D1347, D1348,
  D1353).
- **The call is an ordinary application** of the function to every
  argument, the helper calls included. The kernel, the machine and the
  native backend see nothing new.

## 5. Writing defaults

### 5.1 Where

```
def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat := …

def sumTo (n: Nat): Nat :=
  def go (k: Nat) (acc: Nat := 0): Nat := …     -- a local definition
  go n
```

- An explicit header parameter of a `def` or `theorem`, top-level or local.
  `(a b: Nat := 0)` gives each its own default, the same expression, as
  fields do.
- **Not** an implicit or `auto` parameter (`[n: Nat := 0]` stays `E-PARSE`):
  an implicit is found by unification and an `auto` by search, and
  `[x := e]` already overrides either (`named-arguments.md` §1 non-goals).
- **Not** a lambda's parameter, and **not** a function type. A lambda has no
  declaration to keep a default with, and the only way to call it by name
  is through a `let` or an annotation, whose signature is a type (§4.3 of
  `named-arguments.md`); defaults aren't part of types (D1352). Both are
  `E-PARSE`, "only a definition's parameter or a field can have a default
  value".
- **Not** parameters after the colon, which arms match: a default there
  would have to be a pattern's default. `def f (k: Nat := 3): List Text -> Nat`
  with arms is fine; the default is on `k`.
- **Not** an `instance`'s parameters (all implicit or `auto`), an
  interface's methods (`E-FIELD-DEFAULT`, as now), or a data type's
  parameters.
- **Constructors** already have field defaults. Whether a constructor
  *call* uses them is D1346 (§6.6).

A defaulted parameter may come anywhere in the header, before or after
required ones; since it is named-only (§6.2), its place affects no call.
The style guide says to put defaulted parameters last, as Swift's does.

### 5.2 What a default may use

As for fields (`named-arguments.md` §5.1 rules 2, 5, 8 and 9):

- **Earlier parameters**, explicit, implicit and `auto` alike, and anything
  in scope at the declaration. A later parameter is `E-UNKNOWN-NAME`, with a
  note. So defaults may depend on each other and on earlier required
  parameters:

  ```
  def grid (width: Nat) (height: Nat := width) (fill: Cell := Cell.empty): Grid width height := …

  def padded (n: Nat) (xs: Vec Nat n := Vec.replicate n 0): Vec Nat (n + 2) := …
  ```

- **Row variables.** An ability row is an implicit parameter, so a default's
  type may mention it, and the default may be a function over that row:
  `(onItem: Item -> {e} () := _ => ())` is a pure value (building the
  function performs nothing), usable at any `e`.
- **Checked for every value of the earlier parameters.** The helper takes
  them as parameters of their declared types, so the default can't assume
  an earlier default was used: after `(size: Nat := 8)`,
  `(ok: size = 8 := rfl)` is `E-REFL`, with the note that a call may give
  `size`.
- **Leaving a parameter out commits to its default.** Nothing is inferred
  from the other arguments, by construction (§6.1, "Order of work"). With `def sized (n: Nat := 3) (xs: Vec Nat n)`,
  `sized threeVec` checks and `sized twoVec` is `E-TYPE-MISMATCH`, "`n` is
  left out, so it is its default value, `3`; give `(n := 2)` to use
  another".
- **Not the function itself**, nor a definition in a cycle with it: the
  default is checked before the function's body, from the header alone. A
  name that would make a cycle is `E-MUTUAL-SIGNATURE` with a note, as a
  type that mentions a definition being checked is now
  (`docs/syntax.md:107`) **[checked]**; that this error is the right one
  to reuse is **[inferred]**.
- **Pure** (D1348): elaborated in the empty row, no `Partial`. An operation
  is `E-ABILITY` and a `Partial` call `E-PARTIAL`, with the note "a
  parameter's default can't perform operations: it is computed at each call
  that leaves the parameter out".

### 5.3 When a default is computed

At each call that leaves the parameter out, as part of that call: the call
`makeBooking "a"` is the term `makeBooking "a" (helper₁) (helper₂ …) …`.
Since a default is pure and terminates, whether it is computed once or per
call can't be observed; "per call" is just what the term says, and it is
what Scala, Kotlin, Swift and JavaScript do. There is no shared state to
get wrong, as Python's shared mutable default does.

## 6. Calls

### 6.1 The rule

For a call `h a₁ … aₙ` whose head has a declared signature
(`named-arguments.md` §4.3), with a dot receiver or piped value if there is
one:

1. **Fill slots as now** (D1112), except that a positional argument takes
   the first *required* explicit parameter still free: one without a
   default (D1349). A named argument may fill any parameter, defaulted or
   not.
2. **Fill the defaults.** Every defaulted parameter the call doesn't name
   gets its default: its helper applied to the earlier parameters it needs
   (D1350). This happens at the end of every written call, including a bare
   name (`makeBooking`), dot notation (`clip.trimmed`), a method section
   (`.trimmed`) and a pipe (`clip |> trimmed`).
3. **Left-out required parameters** follow D1095, with each filled default
   counting as given: a required parameter left out *before* the last
   parameter given or defaulted makes the call a function of it, with its
   name, as a rigid variable; one left out after it stays to currying.
4. **Then apply** in parameter order, as a positional call does, with the
   run order of `named-arguments.md` §4.5 unchanged: a default performs
   nothing, so it adds nothing to the trace.

**Order of work.** Leaving a parameter out commits to its default by
construction, not by a check after inference. A call is elaborated in this
order:

1. **Assign the slots, syntactically.** Each parameter is supplied (by a
   positional or named argument), defaulted (not named, and has a default),
   or abstracted into the lambda of rule 3. This looks only at the shape of
   the written arguments (position, name) and the head's signature, never at
   an argument's elaborated type or value.
2. **Put each omitted defaulted parameter's helper call into its slot**,
   before any argument is elaborated. The slot is then a term over the
   earlier slots with no unknown in it.
3. **Only then elaborate the supplied arguments**, each against its expected
   type with the earlier slots substituted.

So in `sized twoVec` the argument `twoVec` is checked against
`Vec Nat (helper)`, and the helper reduces to `3`: the error is a mismatch
of `Vec Nat 2` with `Vec Nat 3`. Had `twoVec` been elaborated against
`Vec Nat ?n` first, unification would set `?n := 2` before the default was
considered, and the call would silently mean `(n := 2)`. The same holds when
the default could only be reached indirectly. With
`def pair (n: Nat := 3) (xs: Vec Nat n) (ys: Vec Nat n)`, the call
`pair (ys := twoVec)` leaves `xs` out before the last given parameter, so it
is a lambda over `xs`, and `n` is still its helper's `3`: `ys` is checked
against `Vec Nat 3` and fails the same way, naming `n` and its default
(§8.3).

Today's order already has this shape. `plan` calls `fill`, which matches
arguments to parameters from their written position and name and the
signature's parameter names alone, without elaborating any argument
(`crates/elab/src/named.rs:156-180`, `:253-305`). The slots are then handed
to `apply_slots` or `apply_args`, which elaborate the arguments afterwards
(`crates/elab/src/check.rs:1296-1302`, `:1312-1318`, `:1370`;
`named.rs:496-523`) **[checked]**. So slot assignment is purely syntactic,
with one exception: the signature is read from the head's type with `force`
(`named.rs:59-102`), and for a type that computes only once arguments are
given (`Signature::stuck`) `split` applies the first arguments before the
rest are matched (`named.rs:215-246`; `check.rs:1289-1295`) **[checked]**.
Defaults are read only from the head's declaration (§7.2), whose signature
is known before any argument, so the exception doesn't reach them
**[inferred]**. The new work is step 2: building the helper-call slots
before `apply_args` runs.

Examples, with `def range (start: Nat) (stop: Nat) (step: Nat := 1)`:

```
range 0 10                -- range 0 10 1                (step's helper, shown here as 1)
range 0 10 (step := 2)    -- range 0 10 2
range (step := 2) 0 10    -- range 0 10 2                (names go anywhere)
range 0                   -- stop => range 0 stop 1      ((stop: Nat) -> List Nat)
range                     -- start stop => range start stop 1
xs.map (range 0)          -- each x: range 0 x 1
range 0 10 2              -- E-DEFAULT-POSITIONAL (§6.3)
```

and with `def sized (n: Nat := 3) (xs: Vec Nat n): Nat`:

```
sized                     -- sized 3                     ((xs: Vec Nat 3) -> Nat): a partial application
sized threeVec            -- sized 3 threeVec
sized (n := 2) twoVec     -- sized 2 twoVec
sized twoVec              -- E-TYPE-MISMATCH: `Vec Nat 2` is not `Vec Nat 3`; `n` is its default
```

`range 0` is a lambda, not the partial application `range 0`, because the
default for `step` sits after the left-out `stop`. That matches D1095:
`clampTo (high := 10)` is already `low value => clampTo low 10 value`. The
lambda and the partial application of the old reading are different
terms, and that's the point: `range 0` now means "the two-argument
`range`, with `start` fixed", which is what a caller of a function with a
default wants.

### 6.2 Positional arguments skip defaulted parameters

**Recommended (D1349): a defaulted parameter is given by name only.** This
keeps D1097's rule 1 from `named-arguments.md` §5.4. Reasons:

- **The arity of a call is visible.** With currying, a short call is a
  function. If positional arguments could fill defaulted parameters, then
  whether `f x y` is a value or still a function would depend on which of
  `f`'s parameters have defaults, and adding a default would change it.
  Named-only means: positional arguments fill exactly the required
  parameters, in order, and the call is a function of the required ones it
  doesn't reach. Nothing about defaults is needed to read it.
- **Adding a default never moves an argument** (`named-arguments.md` goal
  3). Adding a new defaulted parameter anywhere leaves every existing
  positional call as it was. Giving an existing parameter a default makes
  existing positional calls that pass it an error with a fix, not a silent
  change.
- **Kotlin's corner disappears.** A default before a required parameter is
  no different from one after it.
- **It's what the factory wants.** `makeBooking "a" 0.0 30.0` says less
  than `makeBooking "a" (duration := 30.0)`.

The cost is that `range 0 10 2` must be written `range 0 10 (step := 2)`,
which Kotlin, Scala, Lean and JavaScript would all accept positionally.
A second cost falls on existing code: making a required parameter optional
breaks the calls that pass it positionally (§11, "Adding a default to an
existing parameter").

### 6.3 A positional argument after the parameters run out

`range 0 10 2` gives a positional argument when no required parameter is
left. Under §6.1 it would apply the *result*, `range 0 10 1`, to `2`. For a
`List Nat` that is a type error anyway, but for a function whose result is
a function it would check and mean something else:

```
def scaler (base: Nat) (factor: Nat := 1): Nat -> Nat := …

scaler 5 3      -- (scaler 5 1) 3, or scaler 5 3?
```

This is OCaml's ambiguity, made visible. **Recommended (D1351): an error.**
A positional argument written after the header's parameters are used up,
in a call that left a defaulted parameter out, is `E-DEFAULT-POSITIONAL`:

```
E-DEFAULT-POSITIONAL: `3` comes after all of `scaler`'s parameters,
                      but `factor` was left out and has a default
note: to give `factor`, write `scaler 5 (factor := 3)`
note: to apply the result, write `(scaler 5) 3`
```

The brackets say "this call is finished", so `(scaler 5) 3` is `scaler 5 1`
applied to `3`. A call that names every defaulted parameter, or whose head
has none, is unchanged.

### 6.4 Function values and eta-expansion

- **A function's declared type is the full arrow**, defaulted parameters
  included: `range: (start: Nat) -> (stop: Nat) -> (step: Nat) -> List Nat`.
  That is what hover shows (with the defaults written in), what the kernel
  checks and what a theorem about `range` quantifies over.
- **The expression `range` is the call with no arguments** (§6.1), so as a
  value it is `start stop => range start stop 1`, of type
  `(start: Nat) -> (stop: Nat) -> List Nat`. `let g := range` gives `g`
  that type and those names; `g` has no defaults of its own.
- **To pass the function with a default still open**, write the lambda:
  `start stop step => range start stop (step := step)`. No special syntax
  (D1352). Lean's `@f` and Scala's `f _` are the precedents for a bare name
  that doesn't fill; they exist mostly for implicit arguments, which
  Stitchwort fills the same way in both forms. If a real program needs it
  often, `(step := _)` could later mean "leave it open", but `_` means an
  unknown to solve everywhere else, so that is not proposed.
- **Eta.** `range 0` is a lambda (§6.1), and so is the bare name. Conversion
  already treats `x => f x` and `f` as equal (`named-arguments.md` §2.3), so proofs aren't affected; hashes see the lambda
  (`named-arguments.md` §2.3), so `xs.map range0` and `xs.map (range 0)`
  with `def range0 := range 0` are different terms as today.
- **Higher-order code is unchanged.** A parameter of function type, a `let`
  with an annotation, a record field of function type: none can have
  defaults, so a call through them is as today.
- **Inside a group of mutually recursive definitions**, a definition "must be
  given all its arguments" (`docs/syntax.md:108`) **[checked]**. A filled
  default counts as given, so `go rest` with `acc` defaulted is a full call.

### 6.5 Dependent defaults and run order

A default that needs a written argument uses that argument's value. As for
fields (§5.1 rule 1 of `named-arguments.md`), a written argument a default
needs runs once:

```
def framed (title: Text) (width: Nat := title.length + 4): Text := …

def main(): {IO} () :=
  IO.print (framed (readTitle()))    -- reads once: let t := readTitle(); framed t (width default of t)
```

In a computation, an effectful argument already runs first into a variable
(`named-arguments.md` §4.5 step 2), and the helper is applied to that
variable. In pure code, a written argument a default needs that isn't a
variable, a definition's name, a number, text or a constructor without
fields is bound by a transparent `let` first (the same test,
`defaults::simple`, `crates/elab/src/defaults.rs:381-389`) **[checked]**.

A default that needs a left-out required parameter lands inside the lambda
of §6.1 rule 3, where that parameter is bound: `padded` alone is
`n => padded n (Vec.replicate n 0)`. A default runs no operations, so where
it runs doesn't matter; the stage rules (R3, R4) apply to the written
arguments exactly as today.

### 6.6 Constructors

A constructor's fields can already have defaults, used by literals and
named construction (`Circle { radius = 1 }`). Applying the constructor
doesn't use them: `Circle 1 "a"` gives every field, and `Circle (radius := 1)`
is a function still waiting for `id` (`docs/syntax.md:330`) **[checked]**.
Once `def`s have defaults, that is two rules for one spelling:

```
type Shape = | Circle (radius: Nat) (id: Text := "anonymous") | …
def circle (radius: Nat) (id: Text := "anonymous"): Shape := Circle radius id

circle 1                 -- a Shape
Circle 1                 -- today: a function waiting for `id`
```

**Recommended (D1346): one rule.** A constructor call follows §6.1 too, with
its field defaults as the defaults: `Circle 1` is a `Shape` with `id` its
default, `Circle 1 (id := "a")` gives it, and `Circle 1 "a"` is
`E-DEFAULT-POSITIONAL`. Patterns don't change: a constructor pattern still
has one pattern per explicit field (patterns aren't calls, and a pattern
that leaves a field out would have to mean "any value", unlike Lean, see
`named-arguments.md` §5.1 rule 7). This is D1096's reason ("one application
rule everywhere") applied to defaults. It changes the meaning of existing
constructor calls with defaulted fields, so it is its own stage (§9),
after `def` defaults are in use.

## 7. Elaboration, the kernel and proofs

### 7.1 Helpers

Each default becomes a helper definition, built as a field default's is
(`defaults.rs:104-234`) **[checked]**, with the header's parameters before
it as the context instead of the type's parameters and earlier fields:

- elaborated in the empty row, against the parameter's type, after the
  header and before the body (so the body's own recursive calls can use the
  defaults);
- its parameters are the dependency closure of the elaborated default and
  its type (§5.1 rule 5 of `named-arguments.md`), implicit ones staying
  implicit;
- named with a name source can't write. The field helpers' `R.f.default` is
  safe because `R.f` is a projection, but `range.step.default` isn't, since
  a local definition `step` with its own local definition `default` lifts
  to that name (`docs/syntax.md:205`) **[checked]**. The build picks a
  spelling with a character names can't contain;
- kept as metadata of the definition, one entry per header parameter, in
  `Def` beside its other unhashed facts, the way `Data::defaults` sits in
  `Data` (`globals.rs:160-166`) **[checked]**. The check cache stores it
  with the definition (a format change), and the helpers stay out of the
  name table and the library index, as field helpers do
  (`named-arguments.md`, "As built (stage 2)" items 3 and 4).

`FieldDefault` (helper and captures) already has the right shape; it
becomes the one type for both, and `defaults::construct`'s
call-and-`let` logic is shared.

### 7.2 Calls

`named.rs` already turns a call into a list of slots in parameter order and
builds the lambda for left-out parameters (`plan`, `fill`, `bind_missing`,
`named.rs:156-595`) **[checked]**. Defaults add:

- the signature's parameters carry "has a default" (from the head's
  declaration only: a top-level or local `def`, later a constructor);
- positional filling skips them (§6.2), and the excess check (§6.3);
- after filling, each unnamed defaulted slot is filled with the helper
  call, built from the slots it captures; a captured slot that is
  left-out becomes the lambda's variable, as `bind_missing` does now;
- a bare name or dot call whose head has defaults goes through the same
  path with no written arguments.

A head with no defaults takes today's path, so no existing term changes.

### 7.3 The kernel, hashes and identity

**The kernel is unchanged.** It sees a `def` with an ordinary type and
calls that pass every argument. Defaults are elaborator sugar, as named
arguments and field defaults are.

**Identity (D1353): defaults aren't part of the function's hash.** The
function's hash covers its type and body as now; each helper has its own
hash; a call that relies on a default refers to the helper. So:

- changing a default changes the hashes of the helper and of exactly the
  calls that leave that parameter out (and the tests that contain them
  rerun); calls that name it, and the function itself, keep theirs;
- `range 0 10` and `range 0 10 (step := 1)` are definitionally equal (the
  helper unfolds) but not the same term, so not the same hash; the
  distinction of `named-arguments.md` §5.2 carries over;
- two functions differing only in defaults have the same hash. That is
  harmless: definitions are referred to by their declaration (`DefId`),
  never looked up by hash, and the metadata is kept by declaration, as for
  data types (§5.2 of `named-arguments.md`).

**Invariant: nothing that depends on defaults is cached under the
function's hash alone.** Because a function's hash leaves its defaults out,
two functions with the same hash can have different defaults, and a
function's defaults can change while its hash stays. So callers'
elaboration, hover and completion, the JS wrapper and `.d.ts` shape, and
printing (which hides helper calls, D1354) must be keyed by the declaration
and its source, never by the function's hash. This holds today, and stays
true if stage 1 follows the field defaults' design:

- The check cache is keyed by source, not by hash. A namespace's key is a
  BLAKE3 of the compiler build, format, modes, library digest, namespace
  name, the namespace's source and the keys of its dependencies
  (`crates/elab/src/cache/mod.rs:410-445`; `docs/proposals/check-cache.md`
  §2: "the content hash can't be the lookup key for skipping elaboration",
  and §4.2) **[checked]**. A changed default is a changed source text, so
  the namespace and its dependents are re-elaborated and callers see the new
  default.
- `Data::defaults` is "kept by declaration, never hashed"
  (`crates/core/src/globals.rs:204-213`). It is stored in the cache entry of
  the namespace that declares the type and put back when that entry loads
  (`cache/mod.rs:1417-1425`, `:2744-2745`), so it is invalidated with that
  entry **[checked]**. The `Def` metadata for parameter defaults (§7.1) is
  stored the same way **[inferred]**.
- The test cache is keyed by a test's content hash
  (`crates/driver/src/driver.rs:927-932`) **[checked]**. A test's term holds
  the helper calls its calls rely on, and a helper has its own hash, so
  changing a default changes the hash of exactly the tests that use it. This
  is the one place a hash is the key, and it is sound for that reason.
- Hover, completion and printing read the declaration's metadata in the
  current session. I found no cache of them keyed by a function's hash
  (`crates/cli/src/lsp.rs`, `crates/driver/src/live.rs`) **[inferred]**: they
  are rebuilt from the elaborated session, which the check cache restores
  by source key. The JS wrapper and `.d.ts` are likewise generated from the
  declaration in the session that elaborated it **[inferred]**.

The invariant would fail only for a cache that doesn't exist yet: one keyed
by a function's content hash that stores a caller's elaborated form or the
signature shown to users (a content-addressed index of hovers, say). Any
such addition must key on the declaration and its source, or include the
helpers' hashes.

**No binary compatibility question.** Scala's getters and Swift's
copied-into-the-client defaults exist because separately compiled callers
outlive a library change. Stitchwort re-elaborates every caller when a
callee's source changes (the check cache is keyed by source,
`named-arguments.md` §2.3), so a changed default is always seen.

### 7.4 Proofs

- A theorem stated with a call, `range 0 10 = [0, 1, …]`, has the helper in
  its term; `rfl` and other conversion steps unfold it.
- A general lemma (`range.length (a b s: Nat): (range a b s).length = …`,
  or `f.unfold`) matches a call that left `step` out, with `s` the helper
  call, so `rewrite` works on it.
- A lemma stated with the default *value*, `range a b 1`, doesn't match
  syntactically a goal containing `range a b`, since one has `1` and the
  other the helper call. State such lemmas with the call form
  (`range a b`), which elaborates to the same helper call. This is a real,
  small cost, and the reason the printer hides helper calls (§8).
- Generated theorems (`f.unfold`, `T.ext`) take every parameter explicitly
  and have no defaults.

## 8. Backends and tooling

### 8.1 The machine and native code

Nothing changes. Both run elaborated terms, where a call with defaults is
an application to every argument. Helpers are ordinary definitions,
compiled like any other.

### 8.2 JavaScript

An `export def` crosses as an uncurried function with the binder names as
TypeScript parameter names (`named-arguments.md` §2.3) **[checked]**. Three
ways to export defaulted parameters (D1355):

(a) **A trailing options object** for the defaulted parameters, itself
optional, decoded as a record with defaulted fields is (stage 2b): an absent
own property runs the default, a present one is decoded as given, so a
present `undefined` is `None` for an `Option` (D1114).

```ts
export declare function makeRange(
  start: bigint,
  stop: bigint,
  options?: { readonly step?: bigint }
): bigint[];

makeRange(0n, 10n);
makeRange(0n, 10n, { step: 2n });
```

(b) **Optional positional parameters**, `step?: bigint`, the JS default
convention: absent and `undefined` both mean the default. A defaulted
parameter before a required one has to be `T | undefined`, and a defaulted
`Option` parameter can't receive `None`, because `undefined` already means
"use the default".

(c) **Refuse** `export def` with defaults (`E-EXPORT`), and export a wrapper.

The generated type, under `--strict --exactOptionalPropertyTypes` (the flags
the existing `.d.ts` snapshots are checked with,
`crates/cli/tests/extract.rs:140-146`) **[checked]**, needs care for a
defaulted `Option T` parameter, which has three cases: absent means the
default, present as `undefined` means `None`, present as a value means
`Some`. Under `exactOptionalPropertyTypes`, `f?: T` does not accept an
explicit `undefined`, so the property type must admit it: `f?: T | undefined`.
This is the shape already generated for a record's defaulted `Option` field,
`colour?: string | undefined` in `ConfigInput`
(`crates/cli/tests/snapshots/extract__field-defaults.d.ts.snap:12`; D1114;
`named-arguments.md` §5.3, "Absence versus `None`") **[checked]**. For

```
export def tag (name: Text) (colour: Option Text := Some "blue") (size: Nat := 1): Text := …
```

the declarations are

```ts
export type TagOptions = {
  readonly colour?: string | undefined;
  readonly size?: bigint;
};
export declare function tag(name: string, options?: TagOptions): string;
```

`size` is a plain optional property (absent means the default). `colour`
admits `undefined`, which is `None`. Option (b) would have to write
`colour?: string | undefined` too, with `undefined` meaning the default,
which is why (b) can't pass `None`.

**Recommended: (a).** Stitchwort's defaulted parameters are named-only and
order-free, and an options object is the TypeScript way to say exactly
that. It keeps the three meanings of a defaulted `Option` (default, `None`,
`Some`) that D1114 kept for fields, and it reuses the input decoders. The
object's name in the `.d.ts` is `options`, or another free name if a
parameter is called that; it is cosmetic. Results are unaffected: a
function's result has no defaults.

### 8.3 Errors

| Situation | Error |
|---|---|
| A default on an implicit, `auto`, lambda or function-type parameter | `E-PARSE`: "only a definition's parameter or a field can have a default value" |
| A positional argument after the parameters ran out, with a default left out (§6.3) | `E-DEFAULT-POSITIONAL` (new), with both fixes |
| A default that uses a later parameter | `E-UNKNOWN-NAME`, note: "`x` is a later parameter: a default may use only the parameters before it" |
| A default that performs an operation or calls something `Partial` | `E-ABILITY` / `E-PARTIAL`, with the note of §5.2 |
| A default that assumes an earlier default was used | its own error (`E-REFL`, `E-TYPE-MISMATCH`), note: "a default must work for any values of the earlier parameters" |
| A written argument that doesn't fit because a left-out parameter is its default (§5.2) | `E-TYPE-MISMATCH`, note naming the parameter and its default value |
| A name the function doesn't have | `E-UNKNOWN-NAME` as now, listing parameters with their kinds and defaults: `(id)`, `(duration := 60.0)` |
| A call used as a value where a function is expected, or the reverse | `E-TYPE-MISMATCH` with today's "still waiting for" note, which also lists the defaults that were filled: "`range 0` is a function still waiting for `stop`; `step` is its default, `1`" |
| A default that names the function or its cycle | `E-MUTUAL-SIGNATURE`, with a note |

### 8.4 Editor and printing

- **Hover** on a definition shows its header as written, defaults included:
  `def range (start: Nat) (stop: Nat) (step: Nat := 1): List Nat`. Hover on
  a call's head says which defaults the call used.
- **Completion** after `(` already offers parameter names not yet given
  (stage 1b of `named-arguments.md`); defaulted ones show their default,
  `duration := 60.0`.
- **Printing terms (D1354).** In messages, hover and goals, an argument that
  is exactly the call of that parameter's helper (with the captures the
  call would build) is left out, so the goal shows `range 0 10`, not
  `range 0 10 (range…step…default)`. The printed call elaborates back to
  the same term for the same declaration, with the same defaults. `show` on values is unaffected (values have no helper
  calls).
- **The formatter** keeps `(x: T := e)` as written, as it does for fields
  (`crates/fmt/tests/golden/field-defaults.*`); a golden test with a
  multi-line header is enough.
- **Signature help** (the parameter list shown while typing a call) isn't
  offered by the language server today; it is a separate, later piece, and
  would show defaults the same way hover does.

## 9. Staging

| Stage | What | Lane | Size |
|---|---|---|---|
| 1 | `(x: T := e)` on explicit parameters of top-level and local `def` and `theorem` headers; helpers (shared with field defaults); metadata in `Def` and the check cache; calls per §6.1 to §6.5 (named-only, filling at the end of every call including bare names, dot, sections, pipes; lambda for left-out parameters); `E-DEFAULT-POSITIONAL`; the errors of §8.3; hover and completion show defaults; `export def` with a default is `E-EXPORT` ("not yet"); accept example with `makeBooking`, reject examples; `docs/syntax.md` | **Opus** (application spine in `named.rs`, `check.rs`, `dot.rs`, `pipe.rs`) | medium |
| 1b | Printing: leave out helper calls (D1354) in messages, hover and goals | Sonnet | small |
| 2 | JS: the options object (D1355), `.d.ts` snapshots under `tsc --strict --exactOptionalPropertyTypes`, decoder tests | Sonnet | small to medium |
| 3 | Constructor calls use field defaults (D1346); update examples that apply constructors with defaulted fields | Sonnet | small |

Stage 1 alone covers the factory: `makeBooking "a" (duration := 30.0)`,
`.map makeBooking`, dependent and `Option`/list defaults.

**Acceptance invariants**, each a test:

1. (1) A call that names every defaulted parameter is the same term, with
   the same hash, as before the defaults were added.
2. (1) Adding a defaulted parameter to a function leaves every positional
   call of it meaning what it did (or, for a call that ran past the
   parameters, an `E-DEFAULT-POSITIONAL`), never a silent change.
3. (1) Changing a default changes the hashes of exactly the calls that
   leave it out.
4. (1) A written argument that a default uses runs once.
5. (1) A default that assumes an earlier default is refused; leaving a
   parameter out commits to its default.
6. (1) `xs.map f`, `let g := f`, `x.f`, `.f` and `x |> f` with defaulted
   `f` give a function of the required parameters only, with their names.
7. (1) `scaler 5 3` is `E-DEFAULT-POSITIONAL`; `(scaler 5) 3` and
   `scaler 5 (factor := 3)` check and differ.
8. (2) A JS caller can get the default, `None` and `Some` for a defaulted
   `Option` parameter. The generated `.d.ts`, with `colour?: string | undefined`
   in the options object, type-checks under stage 2's existing
   `tsc --strict --exactOptionalPropertyTypes` check, with TypeScript calls
   writing each of the three cases (`{}`, `{ colour: undefined }`,
   `{ colour: "red" }`).
9. (1) Defaults are committed before arguments are elaborated (§6.1). With
   `def sized (n: Nat := 3) (xs: Vec Nat n)` and `two: Vec Nat 2`:
   `sized two` fails with `E-TYPE-MISMATCH` because `Vec Nat 2` is not
   `Vec Nat 3`, and the error names `n` and its default; `sized (n := 2) two`
   checks; `sized three` checks. With
   `def pair (n: Nat := 3) (xs: Vec Nat n) (ys: Vec Nat n)`,
   `pair (ys := two)` fails the same way, and `pair (n := 2) (ys := two)` is a
   function of `xs`.
10. (1) Function values, with `def f (a: A) (b: B := dB) (c: C): R`, and `dB'`
    the helper call for `b` (it unfolds to `dB`):
    - `f`, of type `(a: A) -> (c: C) -> R`, is definitionally equal to
      `(a: A) (c: C) => f a c` and to `(a: A) (c: C) => f a dB' c`. All three
      are the same term, since the bare name is the call with no arguments and
      fills the helper. They have the same hash when elaborated in the same
      way: a bare name or partial call that makes a lambda is wrapped in an
      annotation (`named.rs:510`), and `Term::Ann` is hashed
      (`crates/core/src/hash.rs:585-588`) **[checked]**. Whether a written
      lambda carries one depends on how it is elaborated **[inferred]**, so
      the test elaborates each against the same expected type.
    - `(a: A) (c: C) => f a (b := dB) c` is definitionally equal to those
      (the helper unfolds) and has the same type, but is not the same term and
      has a different hash (`dB` against `dB'`), as `range 0 10` differs
      from `range 0 10 (step := 1)`.
    - `(a: A) (b: B) (c: C) => f a (b := b) c`, of type
      `(a: A) -> (b: B) -> (c: C) -> R`, has a different type from `f`'s, so it
      is equal to none of the above. It is how to keep `b` open.
    - With `range`: `range 0` and `(stop: Nat) => range 0 stop` are
      definitionally equal, the same term and the same hash, both of type
      `(stop: Nat) -> List Nat`. `(stop: Nat) (step: Nat) => range 0 stop (step := step)`
      has type `(stop: Nat) -> (step: Nat) -> List Nat`, so it equals neither;
      it is what the old partial application `range 0` meant (§11).

## 10. Decisions for Matt

**D1345. Where can a default be written?**
(a) **[Recommended]** On explicit parameters of `def` and `theorem` headers,
top-level and local; not on implicit or `auto` parameters, lambdas, function
types or parameters after the colon (§5.1). (b) As (a), and on lambdas'
typed parameters too. (c) As (b), and in function types, like Lean's
`optParam`, so a parameter or annotation can carry defaults.
Reason: a default needs a declaration to belong to; (c) puts defaults in
types, which `named-arguments.md` §1 rules out for names too.

**D1346. Do constructor calls use field defaults?**
(a) **[Recommended]** Yes, by the same rule as `def`s (§6.6): `Circle 1`
is a `Shape` with `id` its default, `Circle 1 "a"` is
`E-DEFAULT-POSITIONAL`; patterns don't change. Built after `def` defaults
(stage 3). (b) No: constructor calls keep giving every field, and defaults
apply only to braces.
Reason: one application rule; otherwise `circle 1` and `Circle 1` mean
different things.

**D1347. What may a default use?**
(a) **[Recommended]** Earlier parameters, explicit, implicit and `auto`
(so row variables in its type), and anything in scope at the declaration;
checked for every value of the earlier parameters; not later parameters
and not the function or its cycle (§5.2). (b) Constants only, no
parameters.
Reason: dependent defaults (`height := width`, `Vec.replicate n 0`) are
useful, and the field rules already keep them sound.

**D1348. May a default perform operations?**
(a) **[Recommended]** No: pure, no `Partial`, computed at each call that
leaves the parameter out, which then can't be observed (§5.2, §5.3).
(b) Yes, operations in the function's own row, run at the call after the
written arguments, in parameter order (Kotlin's `print: Unit? = println(…)`).
(c) Yes, in the caller's row.
Reason: (a) matches field defaults and needs no run-order rules; (b) can be
added later, without breaking anything, if a program needs a default like
`now := Clock.now()`.

**D1349. Can a positional argument fill a defaulted parameter?**
(a) **[Recommended]** No: a defaulted parameter is given by name only;
positional arguments fill the required parameters in order (§6.2).
(b) Yes, in order, as Kotlin, Scala, Lean and JavaScript do; a default
before a required parameter is then usable only by naming the later ones.
Reason: with currying, (a) keeps a call's arity readable without knowing
which parameters have defaults, and adding a default never moves an
argument.

**D1350. When is a default filled in?**
(a) **[Recommended]** At the end of every written call that doesn't name
the parameter, including a bare name, dot calls, sections and pipes; a
required parameter left out before a filled default becomes a lambda's
parameter, as in D1095 (§6.1). This is Lean's rule. (b) Only when the call
gives every required parameter; otherwise the defaulted parameters stay
parameters of the partial application (so `xs.map (range 0)` would need
`step` too). (c) OCaml's rule: when a later positional argument is applied,
so a trailing defaulted parameter can never be filled.
Reason: (a) makes `xs.map makeBooking` and `range 0` the functions a
reader expects, and needs no new idea beyond D1095.

**D1351. A positional argument after the parameters run out, with a
default left out** (`scaler 5 3`, where `scaler`'s result is a function).
(a) **[Recommended]** `E-DEFAULT-POSITIONAL`, with notes to name the
parameter or to bracket the call, `(scaler 5) 3` (§6.3). (b) Allowed: it
applies the result, `(scaler 5 1) 3`.
Reason: (b) is OCaml's silent ambiguity; brackets make the intent
explicit at no cost.

**D1352. Function values and types.**
(a) **[Recommended]** Defaults are never part of a type. The bare name is a
function of the required parameters with defaults filled (D1350); to keep
a defaulted parameter open, write a lambda; no special syntax (§6.4).
(b) As (a), plus a form that doesn't fill defaults (like Lean's `@f`).
(c) Defaults in function types (Lean's `optParam`, TypeScript's `x?`), so
they survive `let` and parameters.
Reason: types stay plain arrows, higher-order code is unchanged; (b) can be
added if a program needs it often.

**D1353. Is a default part of the function's identity?**
(a) **[Recommended]** No, as D1099 decided for fields: each default is a
helper, kept as metadata of the declaration; calls that leave the parameter
out refer to it; changing a default changes exactly those calls' hashes
(§7.3). (b) Yes: changing a default changes the function's hash and
everything that mentions it. (c) No, and each call copies the default's
term instead of calling the helper (Swift's way), so there's nothing to
hover and the term is checked again at every call.
Reason: precise test reruns, one place that defines each default, and the
same design as field defaults.

**D1354. How are filled defaults printed?**
(a) **[Recommended]** Left out: in messages, hover and goals, an argument
that is exactly its parameter's default call isn't shown, so goals read
`range 0 10` (§8.4). (b) Shown as the helper call. (c) Shown as the
default's value, `range 0 10 1`.
Reason: (a) prints what was written and elaborates back to the same term;
(c) would suggest lemmas about `range a b 1` that don't match the goal.

**D1355. JS: how does an exported function take defaulted parameters?**
(a) **[Recommended]** A trailing optional options object holding the
defaulted parameters, decoded like a record with defaulted fields (absent
means the default, `undefined` means `None` for an `Option`, D1114) (§8.2).
(b) Optional positional parameters, `step?: bigint`, where absent and
`undefined` both mean the default. (c) `E-EXPORT`: export a wrapper.
Reason: named-only in Stitchwort is an options object in TypeScript, and it
keeps `None` passable.

**D1356. Staging.**
(a) **[Recommended]** §9: stage 1 is `def` defaults with calls, errors,
hover and completion (enough for `makeBooking`), with exports refused;
then printing, then JS, then constructor calls. (b) Everything in one stage.
Reason: stage 1 is the part the factories need; the rest builds on it without
changing it.

## 11. Risks

- **`range 0` changes from a partial application to a lambda** for
  functions that have defaults. Terms and hashes differ from what the same
  text gave before the function had defaults. Conversion treats them as
  equal, so only hashes and printing see it.
- **Adding a default to an existing parameter breaks its positional
  calls.** Defaulted parameters are named-only (D1349), so
  `def retry (attempts: Nat)` becoming `(attempts: Nat := 3)` turns
  `retry 5` into an error, which must become `retry (attempts := 5)`. The
  error is `E-DEFAULT-POSITIONAL` when `retry`'s result is a function (§6.3)
  and otherwise a type error at the extra argument; both notes say to name the
  parameter. The break is diagnosed and mechanical, never silent: every call
  that passes the parameter positionally changes in the same way. Adding a
  default normally feels like relaxing a signature, but here it changes how
  the parameter is passed. Adding a *new* defaulted parameter breaks
  nothing (invariant 2).
- **Named-only surprises people from Kotlin and Scala**, who expect
  `range 0 10 2` to work. The error says exactly what to write.
- **Lemmas about default values** (`range a b 1`) don't match calls that
  leave the parameter out (§7.4). D1354 (a) keeps goals in the call form,
  which steers lemmas the right way.
- **Hidden arguments in proofs.** A goal's printed call hides its defaults
  (D1354). When a proof depends on a default's value, `unfold` of the
  helper is needed; the hover on the call names it.
- **Two kinds of defaults** (fields and parameters) with one set of rules
  is the aim; D1346 (b) would leave a visible difference for constructors.

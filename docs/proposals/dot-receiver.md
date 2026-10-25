# Where does `x` go in `x.f a`? (D302)

**Status:** design note, 21 October 2026. The decisions are D303–D321 (§8).
Measurements are in the appendix.

**As built (rule E, D303–D309):** the elaborator, std, examples, aoc and
the docs follow §5–7. The value before `.f` or `|>` is the first explicit
argument; `E-DOT-NO-RECEIVER` covers a function whose first explicit
parameter isn't the receiver's type; `E-DOT-PARTIAL` is gone (`t.split` is
`Text.split t`); `W-RECEIVER-NOT-FIRST` warns at the definition (an error in
a library file), and `@[noReceiver]` opts a helper out. A method section
follows the dot rule, and with no arguments over a function whose only
explicit parameter is the receiver it is `T.f` itself. The user-facing
description is in `docs/syntax.md` ("`e.name`", "Pipe forward", "Method
sections") and `docs/guide/` chapters 4 and 6.

## 1. The problem in one screen

Dot notation `x.f a` calls `T.f`, where `T` is the head of `x`'s type. Today
`x` goes into **the first explicit parameter whose type has `T` as its head**
(`receiver_place` in `crates/elab/src/dot.rs`). The library puts the main
value **last**, so that the pipe `x |> f a` (which is `f a x`) reads well
(`docs/syntax.md`, "Library convention").

These two rules disagree whenever a function takes two values of the
receiver's type. Here is what today's `target/release/stitchwort` prints for
each line (scratch file, run through the REPL):

```
10 |> Nat.sub 3                -- 0        (Nat.sub 3 10)
(10: Nat).sub 3                -- 7        (Nat.sub 10 3)
[1, 2] |> List.append [3]      -- [3, 1, 2]
[1, 2].append [3]              -- [1, 2, 3]
[1, 2] |> .append [3]          -- [1, 2, 3]   (a method section is dot notation)
"a,b" |> Text.splitOn ","      -- ["a", "b"]
"a,b".splitOn ","              -- [","]       (splits "," on "a,b")
"abc".contains "b"             -- False       (asks whether "b" contains "abc")
"L68".stripPrefix "L"          -- None
```

Every line type-checks. The wrong answers are silent. The same expression
shape, "a value, then `f`, then an argument", gives different results
depending on whether it's written with `.`, `|> .` or `|>`.

Neither "first" nor "last" works for every function:

- **Operator-like** functions take their operands in the order you'd write
  them with an operator: `Nat.sub a b` is `a - b`, `List.append xs ys` is
  `xs ++ ys`, `Text.less a b` is `a < b`, `Eq.trans p q`. For these, `x.f y`
  must mean `f x y`: the **first** parameter.
- **Subject-and-pattern** functions put the pattern first and the subject
  last, for pipes: `Text.stripPrefix prefix t`, `Text.splitOn sep t`. For
  these, `t.f p` must mean `f p t`: the **last** parameter.

The measurements (appendix A) show where the risk is. 95 library functions
take two or more explicit values of their own namespace's type. Only **6**
of them are subject-and-pattern: `Text.stripPrefix`, `stripSuffix`,
`startsWith`, `endsWith`, `contains` and `splitOn`. Today's "first" rule is
right for the other 89. The pipe has the opposite problem: it's right for
those 6 and silently wrong for operator-like functions with arguments
(`|> Nat.sub 3`, `|> List.append ys`). Code in the repository currently
avoids both traps. No dot call goes to one of the 6, and only one pipe goes
to an operator-like function: `5 |> Nat.add 1`, which is commutative.
Anyone new will hit them, though.

The goal (Matt's) is **one rule a reader can apply to any signature, with no
silent misreadings.**

## 2. What other languages do

The question is always the same: given `x.f(a)` or `x |> f(a)`, which
parameter does `x` fill? There are three families.

### 2.1 Receiver first, found by position (data-first libraries)

| Language | `x.f a` means | Pipe | Library order |
|---|---|---|---|
| **Koka** | `f(x, a)`, for any function `f` in scope ([book, "Dot selection"](https://koka-lang.github.io/koka/doc/book.html)) | none needed | data first, function last (`xs.map(fn(x) ...)`), so trailing lambdas work |
| **Nim** | `f(x, a)` ("method call syntax", [manual](https://nim-lang.org/docs/manual.html#procedures-method-call-syntax)) | none | data first |
| **D** | `f(x, a)` (UFCS, [spec](https://dlang.org/spec/function.html#pseudo-member)) | none | data first (`arr.map!(f)`) |
| **Roc** (new compiler) | `animals.len()` is `List.len(animals)`: the receiver is the first argument of the function in the type's module ([mini-tutorial](https://github.com/roc-lang/roc/blob/main/docs/mini-tutorial-new-compiler.md), [static dispatch issue #7458](https://github.com/roc-lang/roc/issues/7458)) | Roc's old `\|>` also passed the value as the *first* argument | data first |
| **Gleam** | no methods | `a \|> f(b)` is `f(a, b)`. For another position, use a capture `f(b, _)` ([tour](https://tour.gleam.run/functions/pipelines/)) | data first (`list.map(xs, f)`, `string.starts_with(s, prefix)`) |
| **Elixir** | no methods | `x \|> f(a)` is `f(x, a)` ([Kernel.\|>/2](https://hexdocs.pm/elixir/Kernel.html#%7C%3E/2)) | data first (`String.starts_with?(s, prefix)`) |

In every language in this group, the dot (or pipe) and the prefix call put
the value in the same place. `String.starts_with?(s, "L")`,
`s |> String.starts_with?("L")` and Roc's `s.starts_with("L")` all mean the
same thing.

### 2.2 Receiver declared in the definition

| Language | How the receiver is marked | Prefix form |
|---|---|---|
| **Rust** | `fn strip_prefix(&self, p: P)`: `self` must be the first parameter ([reference](https://doc.rust-lang.org/reference/items/associated-items.html#methods)) | `str::strip_prefix(s, "L")`: receiver first |
| **Scala 3** | `extension (t: Text) def stripPrefix(p: Text)` ([reference](https://docs.scala-lang.org/scala3/reference/contextual/extension-methods.html)) | `stripPrefix(t)(p)`: receiver first |
| **Kotlin** | `fun String.removePrefix(prefix: CharSequence)`, where `this` is the receiver ([docs](https://kotlinlang.org/docs/extensions.html)) | receiver first |
| **C#** | `static string M(this string s, ...)`, with `this` on the first parameter ([docs](https://learn.microsoft.com/en-us/dotnet/csharp/programming-guide/classes-and-structs/extension-methods)) | receiver first |
| **Swift** | methods inside `extension String { ... }`, with an implicit `self` | no free-function form |
| **Idris 2** | a function *named* `.f`, such as `(.squared) : Double -> Double`, can be used postfix: `x.squared` ([records reference](https://idris2.readthedocs.io/en/latest/reference/records.html)). Record fields get `.f` automatically | `.squared x`: receiver first |
| **Agda** | postfix projections `r .field`, for record fields only ([record types](https://agda.readthedocs.io/en/latest/language/record-types.html)) | n/a |

Declaring the receiver removes any guessing. Even so, every one of these
languages puts the declared receiver **first** in the prefix form.

### 2.3 Receiver found by type (Lean)

**Lean 4** resolves `e.f` by looking up `f` in the namespace of the head of
`e`'s type. The value goes into "the first explicit argument" of that type
([reference §"Generalized field notation"](https://lean-lang.org/doc/reference/latest/Terms/Function-Application/#generalized-field-notation)).
This is Stitchwort's rule A. The reference gives no tie-breaking rule and no
warning for several candidates. Instead, Lean's library is written so that
"first" is right. The examined value comes first:
`String.dropPrefix? (s : String) (pat : ρ)`
([Strings](https://lean-lang.org/doc/reference/latest/Basic-Types/Strings/)).
Two-sided functions are named so that `x.f y` reads as a sentence:
`" ".isPrefixOf name` (the reference's own example). Lean also has both
pipes. `x |> f` applies `f`, and `e |>.f a` is `(e).f a` (the same as
Stitchwort's `|> .f a`). Lean's library still has higher-order functions
first (`List.map f l`). Lean gets away with that because the type scan skips
over `f`.

### 2.4 No methods; pipe into the last argument (data-last libraries)

**F#** ([pipelines](https://learn.microsoft.com/en-us/dotnet/fsharp/language-reference/functions/)),
**OCaml**'s stdlib, **Elm**, **Haskell** (`&` from `Data.Function`; the
record dot of `OverloadedRecordDot` reads fields only) and **Unison** have no
UFCS. Their `x |> f a` is `f a x`, so libraries put the data last
(`List.map f xs`), which also makes partial application (`List.map f`)
useful. The known gotcha is Stitchwort's: in Elm or F#,
`xs |> List.append ys` is `ys ++ xs`. **OCaml's Jane Street `Base`** went the
other way. It is data-first with labelled arguments (`List.map l ~f`), which
makes the order irrelevant for everything but the data.

### 2.5 What this tells us

- Everywhere the dot exists, the receiver is the **first** argument of the
  prefix form, whether found by position (Koka, Nim, D, Roc), declared
  (Rust, Scala, Kotlin, C#) or found by type with a data-first library
  (Lean). No language found puts a dot receiver last.
- Languages that have **both** a dot and a pipe either make the pipe
  data-first too (Roc's old pipe; Gleam and Elixir have no dot but are
  data-first for the same reason) or keep the pipe last and add a separate
  "method pipe" (Lean `|>.`). Stitchwort is currently the Lean shape with an
  F# library order, which is the one combination where the forms disagree.

## 3. What Stitchwort does today, exactly

- **Dot:** `x.f a…` scans `T.f`'s explicit parameters for the first whose
  type has head `T` (following nicknames), puts `x` there, and fills the
  others in order. `t.split` with nothing after it becomes
  `c => Text.split c t`, a special case for "parameters left out before the
  receiver" (`docs/syntax.md`, `e.name`).
- **Method section:** `.f a` is `x => x.f a`, and `x |> .f a` is rewritten
  by the parser to exactly `x.f a`, so it follows the dot rule.
- **Pipe:** `x |> f a b` is `f a b x`. `x` is checked first and unified with
  the **last** parameter (`crates/elab/src/pipe.rs`).
- **Library:** main value last. 101 of the 283 library definitions that
  take a value of their own type take it somewhere other than first
  (appendix B).

Today's code uses dot calls and method sections far more than pipes into
qualified names. Across `examples/` and `aoc/`, the index finds 1,561 dot
calls and sections, and 57 pipes into a qualified library function
(appendix C).

## 4. The candidates

The criteria: can a reader place `x` from the signature alone; can it
silently misread; do `.f`, `|> .f` and `|>` agree; what it forces on the
library order; dependent types; effects; error messages; and migration cost.

### A. First parameter of type `T` (today)

- Reader: must scan the parameter types. Usually easy, but it depends on how
  nicknames unfold.
- Silent misreadings: yes. 6 library functions are wrong today
  (`stripPrefix` …), and any future subject-and-pattern function is too.
- `.f` and `|>` disagree for every 2+-argument function, as shown in §1.
- Cost: none.

### B. Last parameter of type `T`

- Fixes the 6 Text functions and silently breaks the 89 operator-like ones:
  `a.sub b` would become `b - a`, `xs.append ys` would become `ys ++ xs`,
  and `a.less b` would become `b < a`.
- Changes 20 existing dot calls (appendix C).
- Rejected: it moves the trap rather than removing it.

### C. Two or more parameters of type `T` is an error

- Reader: no misreading possible. Any doubt becomes an error ("`Text.splitOn`
  takes two `Text`s; write `Text.splitOn "," t` or `t |> Text.splitOn ","`").
- Bans the natural `xs.append ys`, `a.max b`, `p.trans q` and `a.less b`, so
  the 20 existing dot calls to those functions must be rewritten.
- Leaves the dot and the pipe reading differently, and leaves the type scan.
- A good **guard**, but not a rule anyone would design on purpose.

### D. A declared receiver (Scala/Kotlin/Rust style), with C for unmarked functions

For example, `def Text.stripPrefix (prefix: Text) (self t: Text)`, or
`def (t: Text).stripPrefix (prefix: Text)`.

- Reader: unambiguous, but only by looking at the definition. Two orders
  have to be remembered per function: `t.stripPrefix "L"`, but
  `Text.stripPrefix "L" t` when written in full.
- Needs new syntax and a marker on every function used with dot that has 2+
  `T` parameters.
- If the receiver is declared up front (`(t: Text).stripPrefix`), the only
  natural prefix order is receiver-first. Every language in §2.2 does that,
  and then this is candidate E with extra syntax.
- Operator-like functions still read backwards in pipes.

### E. Receiver = the first explicit parameter, full stop (and the pipe agrees)

`x.f a b` is `T.f x a b`. `x |> g a b` is `g x a b`. The library is
data-first.

- Reader: places `x` without looking at any types. The dot, `|> .f`, `|>`
  and the prefix form all put the value in the same place.
- Silent misreadings: none from the rule itself. If `T.f`'s first explicit
  parameter isn't a `T`, it's an error, not a search. The only remaining
  risk is a library author choosing a bad order, and a definition-time check
  catches the common case (§6).
- Library order: main value first, other arguments after it, functions
  last. 67 public library functions change (appendix B).
- Partial application `List.map f` stops being useful. Method sections
  replace it: `lines.map (.splitOn ",")`. Stitchwort already has these.
- Cost: about 1,400 prefix references to the reordered functions get their
  arguments swapped, mostly in proofs (appendix B). Pipes into the reordered
  functions keep their text and their meaning, as do dot calls and method
  sections.

### E′. E for the dot, but the pipe stays "last" (Lean's shape)

- `|>` stays plain function application, and the library is data-first, so
  `xs |> List.map f` becomes a type error (`f` isn't a list). The real
  problem is `t |> Text.stripPrefix "L"`. With the reordered
  `stripPrefix (t) (prefix)`, it becomes `stripPrefix "L" t`, which is
  **silently wrong** (both are `Text`). That would hit all 57 existing pipes
  into library functions, and every F#-style habit after them.
- Rejected: it recreates the problem for pipes.

### F. Receiver = the last explicit parameter, for dot and pipe

`x.f a b` is `T.f a b x`, with data last everywhere.

- Reader: places `x` without types, and the dot and pipe agree.
- Silent misreadings: every operator-like function reads backwards unless
  its meaning is flipped. `a.sub b` would be `Nat.sub b a`, so either
  `Nat.sub 3 10` must mean `10 - 3`, or `a.sub b` means `b - a`. The same
  goes for `append`, `less`, `compare`, `zip`, `divides`, `pow` and
  `Eq.trans`.
- Dependent types: the receiver can't come first when a later parameter's
  type mentions it. Examples are `List.get (xs: List a) (i: Fin xs.length)`
  and today's `Vec.getLt (v: Vec a n) (i: Nat) [auto ok: i < n]`. Under F
  these need workarounds.
- Changes the meaning of 152 existing dot calls (appendix C), and 38
  functions need reordering.
- Rejected.

### Comparison

| | A today | B | C | D | **E** | E′ | F |
|---|---|---|---|---|---|---|---|
| Place `x` without reading types | no | no | no | no | **yes** | yes (dot) | yes |
| Silent misreading possible | yes (6 fns) | yes (89 fns) | no | no | **no** | yes (pipes) | yes (operators) |
| `.f`, `\|> .f`, `\|>` and prefix agree | no | no | no | no | **yes** | no | partly |
| Library order | data last | data last | data last | either | **data first** | data first | data last |
| Dependent "index after subject" signatures | exception | exception | exception | fine | **natural** | natural | awkward |
| New syntax | — | — | — | yes | **—** | — | — |
| Library signatures changed | 0 | 0 | 0 | ~6–95 markers | **67 (+40 helpers, optional)** | 67 | 38 |
| Existing call sites changed | 0 | 20 | 20 | ~0 | **~1,400 prefix (mechanical), 1 pipe** | ~1,400 + 57 pipes | 152 dot |

## 5. Recommendation: E, "the value goes first"

> **The value before `.f` or `|>` becomes the first explicit argument:
> `x.f a b` is `T.f x a b` (with `T` the head of `x`'s type), and
> `x |> g a b` is `g x a b`.**

That's the whole rule. No types are scanned, no parameters are skipped, and
there's nothing to remember per function. It is Koka's, Nim's, D's and
Roc's dot, and Gleam's and Elixir's pipe. It's also what Lean's rule
produces on Lean's (receiver-first) library.

**Library convention** (replacing `docs/syntax.md`'s "main value last"): a
function's **main value comes first**, then the other arguments, then any
function arguments. So `xs.foldLeft 0 (acc x => …)` ends with the lambda,
which suits multi-line lambdas. Name two-sided functions so that `x.f y`
reads as a sentence: `t.startsWith p`, `a.sub b`, `xs.append ys`,
`p.isPrefixOf t`.

**How `|>` relates:** `|>` and `.` now differ only in how the function is
found. `x.f a` looks `f` up in `x`'s type's namespace. `x |> g a` uses the
`g` you wrote. `x |> .f a` stays as it is (still exactly `x.f a`), and now
means the same as `x |> T.f a`. A pipe into anything that isn't an
application (`x |> g`, `x |> y => …`) is `g x`, as now. Effects are
unchanged: the left side runs first, then the written arguments, then the
call.

**Why not keep data-last and fix only the six Text functions?** Because the
dot and the pipe would still disagree for every 2+-argument function
(`|> Nat.sub 3` against `.sub 3`). The rule would stay "scan the types,
first match", which a reader can't apply without the signature in front of
them. And every new subject-and-pattern function would be a fresh trap.
Fixing six functions would treat the symptom rather than the cause.

**What we give up:** partial application of data-last functions as values
(`List.map f`, `Text.splitOn ","`). Method sections already cover this
(`.map f`, `.splitOn ","`), and they read the same as the dot. The pipe
also becomes slightly unusual among *curried* languages: F#, OCaml, Elm and
Haskell pipe last. That's a real cost for readers coming from those
languages. It's the same choice Gleam, Elixir and old Roc made, and the
docs can say it in one line.

### 5.1 Before and after

| | Today | After (E) |
|---|---|---|
| **stripPrefix** | `def Text.stripPrefix (prefix: Text) (t: Text)`; `"L68".stripPrefix "L"` = `None` (silently); `line \|> Text.stripPrefix "L"` = `Some "68"` | `def Text.stripPrefix (t: Text) (prefix: Text)`; `"L68".stripPrefix "L"` = `line \|> Text.stripPrefix "L"` = `Text.stripPrefix "L68" "L"` = `Some "68"` |
| **append** | `List.append xs ys` = `xs ++ ys` = `xs.append ys`, but `xs \|> List.append ys` = `ys ++ xs` | unchanged signature; all three forms are `xs ++ ys` |
| **List.map** | `def List.map (f: a -> b) (xs: List a)`; `List.map f xs`, `xs.map f`, `xs \|> List.map f` | `def List.map (xs: List a) (f: a -> b)`; `List.map xs f`, `xs.map f`, `xs \|> List.map f` (dot and pipe text unchanged); as a value: `.map f` |
| **List.foldLeft** | `(f: b -> a -> b) (init: b) (xs: List a)`; `xs.foldLeft f 0` | `(xs: List a) (init: b) (f: b -> a -> b)`; `xs.foldLeft 0 (acc x => acc + x)` |
| **Map.insert** | `(key: k) (value: v) (m: Map k v)`; `m.insert k v`, `m \|> Map.insert k v` | `(m: Map k v) (key: k) (value: v)`; same dot and pipe text |
| **Text.splitOn** | `(sep: Text) (t: Text)`; `"a,b".splitOn ","` = `[","]` (silently) | `(t: Text) (sep: Text)`; `"a,b".splitOn ","` = `["a", "b"]` |
| **List.zipWith** | `(f: a -> b -> c) (xs: List a) (ys: List b)`; `xs.zipWith f ys` | `(xs: List a) (ys: List b) (f: a -> b -> c)`; `xs.zipWith ys (x y => x + y)` |
| **Vec.get** (dependent) | `Vec a n -> Fin n -> a`, already data-first: `v.get i`, but `v \|> Vec.get i` is a type error | unchanged; `v.get i` = `v \|> Vec.get i` |
| **Sized.read** (`examples/accept/dot-notation.sw`) | `def Sized.read (n: Nat) (s: Sized n)`; `s.read 3`, where the receiver's type depends on an earlier explicit argument | `def Sized.read [n: Nat] (s: Sized n)`; `s.read` |

### 5.2 Dependent types, implicits, effects

- **Implicit and `auto` parameters** before the first explicit one are
  inserted as now. "First explicit" ignores them. `Set.insert [auto ord: Ord
  k] (s: Set k) (key: k)` gives `s.insert 3`.
- **Later parameters that depend on the receiver** are natural, because the
  receiver comes first: `List.getLt (xs: List a) (i: Nat) [auto ok: i <
  xs.length]`. Today's data-last convention makes these exceptions (`Vec.getLt`
  is already receiver-first for this reason). Elaboration also gets simpler.
  The receiver is checked first, which is already what dot notation and pipes
  do specially. The "lambda checked after later arguments" rule (SW-129) is
  needed less, because lambdas now come after the data in prefix calls too.
- **A receiver whose type mentions an earlier explicit argument**
  (`Sized.read (n: Nat) (s: Sized n)`) has to make that argument implicit.
  That is better anyway, since `s.read 3` asked for a value the type already
  knows.
- **Type only inside**: a parameter of type `List (List a)` has head `List`.
  One of type `Option T` has head `Option`, so it doesn't count as a `T`.
  Under E this only affects the error message, because nothing is searched.
- **Nicknames**: `p: Price` tries `Price.f`, then `Nat.f`, as today. The
  first explicit parameter is then checked against `p` as usual.
- **Effects and abilities**: unchanged. `Option.orAbort` stays the dot
  spelling of `Abort.need`.
- **Partial dot calls**: `t.split` becomes plain currying, `Text.split t`,
  which is a `Char -> List Text`. The special "parameters left out before
  the receiver" case and its lambda go away. `prefix_form` becomes "put
  `recv` first".

## 6. Error messages

1. **Dot on a function whose first explicit parameter isn't the receiver's
   type** (`E-DOT-NO-RECEIVER`, reworded):
   ```
   error[E-DOT-NO-RECEIVER]: `Nat.firstFrom` doesn't take a `Nat` first, so `n.firstFrom` can't put `n` there
     = `Nat.firstFrom: (Nat -> Bool) -> Nat -> Nat -> Nat`
     = note: dot notation passes the value as the first argument; call it directly: `Nat.firstFrom q n m`
   ```
2. **Pipe into the wrong type**: the existing `E-TYPE-MISMATCH`, now about
   the *first* argument: "`|>` passes the value as the first argument of
   `List.map`, which takes `List a`; the value before `|>` has type `Text`".
3. **Definition-time warning** for namespace functions that take a `T`, but
   not first (`W-RECEIVER-NOT-FIRST`):
   ```
   warning[W-RECEIVER-NOT-FIRST]: `Text.stripPrefix` takes a `Text` but not as its first parameter, so `t.stripPrefix` and `t |> Text.stripPrefix` won't work
     = note: put the main value first: `def Text.stripPrefix (t: Text) (prefix: Text)`
   ```
   This catches the one remaining way to get a misreading: an author
   writing the pattern before the subject. It can't catch an author who
   puts the wrong one of two `Text`s first, because they have the same type.
   Naming guidance and tests have to cover that (§5). The warning is off for
   functions with no explicit parameter of type `T` (constructors-like
   functions such as `List.replicate`). It is also off for library-internal
   helpers that opt out: decision D309.
4. **Old-order calls after the migration**: `List.map f xs` is an ordinary
   type mismatch on `f`. No special "did you mean the old order" message is
   added, following "no transition paths".

## 7. Migration plan

Measured with the code-navigation index over `crates/elab/src/std/`,
`examples/` and `aoc/` (appendix D says how).

1. **Elaborator** (`dot.rs`, `pipe.rs`, the parser's pipe-section rewrite is
   unchanged). In `receiver_place`, return the first explicit parameter, and
   keep the head test only for the error message. Remove the "parameters
   before the receiver" lambda case from `call` and `prefix_form`. In
   `pipe.rs`, unify with the first explicit parameter instead of the last.
   Add the warning. Update `examples/accept/pipe.sw` (its header and
   `5 |> Nat.add 1`), `dot-notation.sw`, `dot-partial.sw` and
   `dot-dependent-mismatch.sw`.
2. **Library order**: reorder the **67 public functions** in appendix B.1.
   The 40 internal helpers and `Prop`s in B.2 (comparators, `Map.Tree.*`,
   `List.All p xs` …) aren't dot-called. Reorder them only where it reads
   better, otherwise mark them as opting out of the warning.
3. **Call sites**: about **1,391 prefix references** to the 67 functions
   need their arguments swapped (std 663, aoc 661, examples 67). 642 of the
   aoc ones are in `Proofs/` folders, mostly `List.sumBy` (365),
   `List.getOr` (188), `List.map` (166) and `List.take` (94). Another ~47 are
   in `Aoc.Day06.Proofs`, which the index tool couldn't load (appendix D).
   Partial applications used as values become method sections. Dot calls
   (273) and pipes (51) into these functions keep their text and meaning.
   The one pipe whose meaning changes is `5 |> Nat.add 1` (commutative).
4. **User functions** in examples/aoc with the main value not first: 7
   (`Bag.map`, `Person.greet`, `Shape.shout`, `Tree.insert`, `Map.insert` in
   an example, `Dial.apply`, `Sized.read`). Two pipes into user functions
   with arguments (`addSay`, `zerosLandedOn`) need checking.
5. **Docs**: `docs/syntax.md` (`e.name`, "Pipe forward", the library
   convention, the Text note that tells readers to avoid `.stripPrefix`),
   namespaces.md §4.8 and the std reference tables.
6. **Order of work**: steps 1–3 must land together, because a half-migrated
   library breaks under either rule. The library and proofs are where the
   volume is. Doing it file by file in parallel lanes, with the gate on the
   merged result, fits how the repository already works.

## 8. Decisions

| ID | Question | Recommendation |
|---|---|---|
| D303 | The rule for dot notation: the receiver is the **first explicit parameter**, with no type scan (E), replacing "first parameter of type `T`" (A)? Rejected: B (last of type `T`), C alone (ambiguity is an error), D (declared receiver), F (always last). | [Yes, E] |
| D304 | Pipe: `x \|> g a b` becomes `g x a b` (first explicit argument), so `.f`, `\|> .f`, `\|>` and the prefix call all agree? (E′, keeping `\|>` last, is rejected because data-first pipes would be silently wrong.) | [Yes] |
| D305 | Library convention: main value first, then other arguments, function arguments last. Two-sided functions are named to read as `x.f y` (`t.startsWith p`, `a.sub b`). This replaces "main value last" in `docs/syntax.md`. | [Yes] |
| D306 | Dot on a function whose first explicit parameter isn't of the receiver's type is an error (`E-DOT-NO-RECEIVER`), never a search for a later parameter? | [Yes] |
| D307 | Definition-time warning `W-RECEIVER-NOT-FIRST` when a function in namespace `T` takes an explicit `T` but not first? | [Yes, warning, not error] |
| D308 | Theorems follow the same order as the functions they're about (`List.sumByAppend (xs) (ys) (f)`), swapped along with the references in step 3, rather than keeping their current order? | [Yes, swap with the functions; theorems are rarely dot-called (5 calls), so only consistency is at stake] |
| D309 | Internal helpers and `Prop`s in appendix B.2 (comparator-first `decEq`/`compareWith`, `Map.Tree.*`, `List.All p xs`) may keep their order and opt out of the warning, rather than all being reordered? | [Yes, opt out; reorder only where it reads better] |
| D321 | Ship rule C (ambiguous dot is an error) now, as a guard until E lands? | [No: no current code misuses it (0 dot calls to the 6 Text functions); go straight to E. Yes if E isn't scheduled soon, since C costs 20 call-site rewrites] |

---

## Appendix A. Functions with two or more explicit parameters of their own type

95 library definitions (from the REPL's `:t` for every `def` in
`crates/elab/src/std/`), plus one example (`Main.Point.add`). Placement under
rule A is shown by bucket.

- **Subject-and-pattern, wrong under A (6):** `Text.stripPrefix`,
  `Text.stripSuffix`, `Text.startsWith`, `Text.endsWith`, `Text.contains`,
  `Text.splitOn`.
- **Operator-like, right under A (most of the rest):** `Bool.compare decEq
  xor`; `Char.compare decEq decEqFrom`; `Int.LessEq LessThan add compare
  decEq div fdiv fmod leq less mod mul sub tdiv tmod`; `List.Disjoint Perm
  Subsequence append reverseOnto zip`; `Map.union`; `Nat.LessEq LessThan
  absDiff add compare decEq decEqFrom div divides equal leq max min mod mul
  pow span sub`; `Ordering.andThen bothEqual compare decEq`;
  `Set.difference intersect union`; `Text.append compare decEq decEqFrom
  less`.
- **Function argument first, then two values in order (right under A):**
  `List.zipWith zipWith3 compareLex decEq merge`, `Vec.zipWith zipWith3`,
  `Option.compareWith decEq`, `Pair.compareWith decEq`, `List.decCons`.
- **Internal helpers:** `List.buildRuns closeGroup mergeRuns pushRun`,
  `Map.Tree.balance bin deleteMin doubleL doubleR glue rebuild shape singleL
  singleR`, `Nat.digitsFuel digitsOnto divFuel firstFrom isRun`.

There are also 277 theorems with two or more such parameters (`Eq.trans`,
`Int.addComm`, `List.appendAssoc` …). They're almost never dot-called.

**Existing dot calls to these functions (20, all right under A):**
`[1, 2].zip [3, 4]` (×5: `examples/accept/dot-prefix.sw:13`,
`eqeq-containers.sw:27`, `list-toolkit.sw:29,101`); `.zipWith` (×2:
`list-toolkit.sw:31`, `aoc/src/Aoc/Day01/Day01.sw:44`); `.zipWith3` (×5,
`list-toolkit.sw:33–41`); `xs.append …` (×4: `implicits.sw:28`,
`match.sw:30`, `mutual-data.sw:131`, `tests.sw:7`); `"…".less "…"` (×5,
`text.sw:9–15`). Under B all 20 change meaning, and under C all 20 are
rejected. Under E all 20 keep their text and meaning.

## Appendix B. Library functions whose main value isn't first

Of 283 library definitions that take an explicit value of their own
namespace's type, 182 take it first, 83 of them as the only explicit
parameter. 101 take it later. With the 6 Text functions, 107 would change
under E.

**B.1 Public, to reorder (67):** `List.all any concatMap count drop elem
filter filterMap find foldLeft foldRight get getOr headOr lookup map
occurrences padRight partition runsCount scanLeft sortBy sortWith splitBy
splitGroups sumBy take zipWith zipWith3`; `Map.adjust alter contains filter
foldLeft get getOr insert insertWith map remove`; `Option.flatMap getOrElse
map`; `Set.contains filter foldLeft insert remove`; `Text.contains drop
endsWith fold padRight split splitOn startsWith stripPrefix stripSuffix
take`; `Vec.any foldLeft headOr map sumBy traverseOption zipWith zipWith3`.

**B.2 Internal or `Prop`, optional (40):** `List.All AllLength Any Groups
LeHead Mem NonSep RunsSorted Sorted SplitKeeps buildRuns compareLex
consSome decCons decEq filterStep merge mergeRuns pushRun transposeN`;
`Map.Tree.Ordered Within doubleR foldLeft get insertWith map minKey
minValue rebuild remove singleR`; `Nat.firstFrom isRun`;
`Option.compareWith decEq showWith`; `Pair.compareWith decEq showWith`.

**Prefix references to B.1 functions (1,391):** by area, std 663, aoc 661
(642 in `Proofs/`), examples 67. The functions with the most references are
`List.sumBy` 365, `List.getOr` 188, `List.map` 166, `List.take` 94,
`List.occurrences` 87, `Option.map` 37, `List.drop` 36, `List.filter` 33,
`List.any` 32, `List.foldLeft` 26, `List.splitGroups` 25 and
`List.filterMap` 25. Including B.2 functions, the total is 1,713.

## Appendix C. Call-site counts by form and rule

References to functions in a namespace `T` that take a `T`, deduplicated by
position. "dot" means `x.f`; a "section" is `.f` (in a pipe or not).

| Area | dot | section | pipe into `T.f` | prefix `T.f …` |
|---|---|---|---|---|
| std | 77 | 0 | 6 | 4,472 |
| examples | 472 | 30 | 47 | 1,122 |
| aoc | 1,004 | 55 | 10 | 3,562 |

(The prefix counts include every mention in theorem statements and proofs.)

| Rule | Existing call sites whose meaning changes or that are rejected |
|---|---|
| B | 20 dot calls (appendix A) |
| C | the same 20, rejected |
| E | 0 dot calls or sections; 1 pipe (`5 \|> Nat.add 1`); ~1,391 prefix calls rewritten as part of the reorder |
| E′ | the ~1,391, plus 51 pipes into reordered functions, silently |
| F | 152 dot calls: `Range.contains` 45, `Dial.move` 24, `Ord` dictionary fields 33, `Dial.zerosDuring` 8, `List.zipWith3` 5, `Text.less` 5, `List.zip` 4, `List.append` 4, `Vec.get` 2, … |

Pipes into qualified library functions today (57 in examples and aoc, 63
including std): `Text.splitOn` 8, `List.map` 7, `Text.stripPrefix` 7,
`List.sum` 5, `Vec.toList` 4, `List.getOr` 4, `Map.insert` 4, `Map.get` 3,
`Text.startsWith` 3, and 18 others. Every one is to a function that E
reorders or that takes one argument, so none changes meaning except
`Nat.add`.

## Appendix D. How this was measured

- **Signatures**: every `def`/`theorem` name in `crates/elab/src/std/`
  (389 defs, 659 theorems), typed with the REPL's `:t Std.<name>`. Explicit
  parameters were split at top-level `->`, skipping `[…]`, and the head was
  taken as the first token, with tuples as `Pair` and `x = y` as `Eq`.
  Nicknames were not unfolded. For example and aoc functions, the types come
  from the index's `symbols`.
- **References**: `stitchwort check --index` per aoc namespace and per
  example file (excluding `reject/`, `soundness/` and `projects/`). The
  index's `refs` cover the library files each one loads. A reference counts
  as dot notation when the character before the name is `.` and what comes
  before that isn't a capitalised namespace path. It counts as a pipe when
  `|>` is the token before the qualified name. Definition sites are
  excluded.
- **Not covered**: `Aoc.Day06.Proofs` could not be indexed. `stitchwort
  check Aoc.Day06.Proofs --index …` panics with "internal error: applying a
  data type" (`crates/core/src/value.rs:480`). Its grep count of prefix calls
  to `List.map`, `sumBy`, `getOr` and similar functions is about 47, and it
  has no dot calls to the 95 functions. The counts are heuristic to within a
  few per cent. They are good enough for sizing, not for an automatic
  rewrite.
- Scripts: `sigs.py`, `measure.py` and `rules.py` in the session scratchpad
  (not committed).

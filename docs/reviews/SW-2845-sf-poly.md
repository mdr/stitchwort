# SW-2845: porting Software Foundations, chapter Poly

**Status:** lane report, 11 November 2026. Ports chapter 4 of *Software
Foundations*, Volume 1: *Logical Foundations* (`Poly.v`, "Poly:
Polymorphism and Higher-Order Functions") to `sf/` as `Sf.Lf.Poly`,
following [SW-2836](SW-2836-sf-lists.md) (Lists) and
[SW-2707](SW-2707-software-foundations-port.md) (Basics, Induction), on
the book's own polymorphic lists (D3512) and numbers (SW-2763).

How claims are marked: **[measured]** run today with the release CLI built
from this branch; **[read]** read in the book's sources or this repo;
**[estimated]** my judgement.

## 1. Summary

- **The whole chapter is ported.** Every definition, every worked example
  and theorem the book proves (34 of 34, plus one of the port's own), and
  every exercise (20, as 29 statements and 11 functions to write), in the
  book's order and sections. `stitchwort check` in `sf/` passes in about
  1.6 s with 178 open goals (40 of them this chapter's), and `stitchwort
  test` passes 12 tests **[measured]**.
- **Polymorphism ports well, and is lighter than in Rocq.** A data
  type's parameters are always implicit in its constructors, and a
  lower-case name used as a type in a header is bound implicitly by
  itself, so the book's three stages (explicit `nil nat`, holes `nil _`,
  `Arguments nil {X}`) end where Stitchwort starts: `Cons (ofNat 3) Nil`.
  Higher-order functions, lambdas, partial application, `fold` and the
  Church numerals all go through as written, every worked proof by `rfl`.
- **What hurts:** the same list notation gap as Lists, now for lists of
  lists too (`ofList [ofNats [1], ofNats [2, 3]]`) (§5.1); the parts of the
  chapter *about* explicit type arguments, which can't be shown because
  constructors have no explicit or named form (§5.2); `repl` and `eval`
  don't load a project, so the book's `Check` and `Compute` have no
  working counterpart in `sf/` (§5.3, a finding beyond this chapter); and
  proofs that compute through a reader's unfinished function pass silently,
  even contradictory ones (§5.4).
- **I solved every exercise in the scratchpad** (not committed): all 40
  goals closed on the first run, `check` 138 goals open afterwards, the
  count without Poly's **[measured]**.

## 2. What was ported

| | Poly.v |
|---|---|
| Book: lines, exercises | 1,246, 20 |
| Book: proved theorems (`Qed`) | 34 |
| Port: files, lines | 5, 930 |
| Data types | 6 and a synonym: `BoolList`, `List`, `Prod`, `Mumble`, `Grumble`, `Option` (OptionPlayground's), `CNat` |
| Definitions (not exercises) | 34, plus `ofList` and `ofNats` (the port's literal helpers) |
| Worked theorems | 35: the book's 34 and `list123Same` |
| Exercises stated | 20: 29 statements, 11 functions |

- **Files.** As before, a book module is a namespace in its own file:
  `Poly.sw` (`Sf.Lf.Poly`, the chapter up to "Functions That Construct
  Functions"), `MumbleGrumble.sw`, `OptionPlayground.sw`, `Exercises.sw`
  (`Sf.Lf.Poly.Exercises`, the Additional Exercises) and `Church.sw`
  (`Sf.Lf.Poly.Exercises.Church`, nested as the book's `Module Church` is
  inside `Exercises`). Each file's header says where it comes in, and the
  README's table gives the order.
- **Imports.** `From LF Require Export Lists` is `import Sf.Lf.Nat (..)`,
  `Sf.Lf.Basics (..)`, `Sf.Lf.Induction (..)` and `Sf.Lf.Lists (..)`
  (`Lists`' top level; the book's `NatList` module isn't exported either,
  so `NatList`'s `Pair`, `Nil` and the rest don't clash). `Church.sw`
  imports only `Nat`, `O`, `S` and `doit3times`, because it defines its
  own `plus`, `mult` and `exp`.
- **Options** are the library's `Option` after OptionPlayground, as the
  book uses Rocq's library `option` there. The book's own lists and pairs
  are its own (`List a` with `Nil`/`Cons`, `Prod a b` with `Pair`), per
  D3512.
- **Names:** `X`, `Y`, `Z` are `a`, `b`, `c` (§5.5); `test` (a keyword) is
  `keep` in `filter` and `partition`; `fold`'s value parameter `b` is
  `init`, since `b` is the type; `mumble`'s constructors `a`–`e` are `A`–`E`.
- **Left out:** the two `manual_grade_for_…` definitions (the grader's),
  `repeat'` without types (a comment: Stitchwort requires them, §3.2),
  `Fail` commands and `Check` commands (comments quoting the error, or
  pointing at `stitchwort doc`). `fold_map_correct`, which the reader
  states, is a comment with the name, as before.

## 3. What ported cleanly, and what came out better

### 3.1 Implicit type arguments

- **A constructor never takes its type's parameters**, and a header's
  lower-case type names are bound implicitly without writing them
  **[measured]**:

  ```
  type List (a: Type) =
    | Nil
    | Cons (x: a) (l: List a)

  def app (l1 l2: List a): List a := match l1 with
    | Nil => l2
    | Cons h t => Cons h (app t l2)
  ```

  is the book's `Fixpoint app {X : Type} (l1 l2 : list X)` after its
  `Arguments nil {X}. Arguments cons {X}.` The port keeps one explicit
  version (`repeat (a: Type)`), one with `_` (`repeat''`) and one with
  `[a: Type]` (`repeat'''`), so the book's progression is still visible.
- **Supplying an implicit by name** is `repeat''' [a := Nat] O O`, where
  Rocq writes `@repeat''' nat 0 0`; it names the parameter, so it doesn't
  depend on position.
- **`doc` shows implicits as the header wrote them** (`def hdError (l:
  List a): Option a`), so the book's `Check @hd_error` needs no `@`.

### 3.2 Higher-order functions

- **Lambdas** are `n => mult n n` (no `fun`), bracketed as arguments; a
  lambda's parameters may be typed, and `fold (l n => plus (length l) n)`
  takes two. Partial application (`plus (ofNat 3)`, `fold plus`) and eta
  (`plus3 = (n => plus (ofNat 3) n)` by `rfl`) work as in Rocq
  **[measured]**.
- **Every worked example is `rfl`**, including `doit3times (n => mult n n)
  (ofNat 2) = ofNat 256` on unary numbers, instantly.
- **`if` on `Bool`** in `filter` is written as in Rocq.

### 3.3 Church numerals

- `CNat` is a type synonym, `type CNat: Type 1 = (a: Type) → (a → a) → a →
  a`, and the numerals and the tests (`plus two three = plus three two`,
  `exp two two = plus two two`) check by `rfl` **[measured, with my
  solutions]**. The book's universe warning has an exact counterpart:
  `two CNat` is `E-UNIVERSE`, "expected something of type `Type`, but
  this has type `Type 1`", quoted in place of Rocq's "Universe
  inconsistency".
- `three := @doit3times` becomes `(a: Type) => doit3times`: the lambda
  takes the type explicitly, and `doit3times` gets it implicitly from its
  expected type.

## 4. The exercises

The chapter's exercises are on the book's `List` and `Prod`, so no std
lemma applies, and `cases` proves none of the eight proof exercises that
don't depend on a function the reader writes: "`cases` found nothing to
split on, and nothing closes the goal" for `appNilR`, `appAssoc`,
`appLength`, `revAppDistr`, `revInvolutive`, `mapRev` and
`foldLengthCorrect` **[measured]**. (`uncurryCurry` and `curryUncurry`
depend on the reader's `prodUncurry`; see §5.4 for what happened there.)

I solved all 40 goals in a scratch copy of `sf/`, nothing of which is
committed or quoted here, in about four minutes, every one first time.
Two notes for a reader:

- The book's hint for `fold_length_correct` and `fold_map` ("`unfold`
  before `simpl`") doesn't apply: the goal computes, so `foldLength l` is
  already `fold … l O`. The port says so in a sentence.
- `mapRev` needs a lemma of the reader's own (`map` over `app`), as the
  book hints.

## 5. Friction, ranked by how much it hurts a reader

### 5.1 No notation for the book's lists, now nested

As in Lists §5.1: list brackets and `++` always mean the library's
`List`. Poly makes it worse, since its examples nest lists and mix
element types **[measured]**:

| Book | Port |
|---|---|
| `[1; 2; 3]` | `ofNats [1, 2, 3]` |
| `[true; false]` | `ofList [True, False]` |
| `[[1]; []; [2;3]; [4]]` | `ofList [ofNats [1], Nil, ofNats [2, 3], ofNats [4]]` |
| `(x, y) :: combine tx ty` | `Cons (Pair x y) (combine tx ty)` |
| `([1;2], [false;false])` | `Pair (ofNats [1, 2]) (ofList [False, False])` |

Two helpers are now needed, `ofList` for any element type and `ofNats`
for the book's numbers, because the numbers need converting too. Goals
print the computed form, so `testHdError2`'s goal is `hdError (Cons (Cons
(S O) Nil) (Cons (Cons (S (S O)) Nil) Nil)) = Some (Cons (S O) Nil)`.
Oddly, `ofNats [1, 5, 4]` was left folded in one goal (`testFlatMap1`)
and unfolded in others, which is consistent with goals keeping calls that
nothing forced, but surprising to read.

The options are Lists §5.1's (a)–(c). With D3512 settled for the port, the
cheapest help is (c), printing a closed `Cons`/`Nil` chain of a
user-defined list-shaped type as a literal and a closed `S`/`O` chain as a
numeral, display only. It would serve every later chapter: Tactics, Logic
and IndProp are full of these goals. Matt's decision (user-visible).

### 5.2 Explicit type arguments can't be shown

The first third of the chapter is about passing types: `nil nat`, `cons
nat 3 (nil nat)`, `@nil nat`, `Fail Check (nil nat)`, and the
mumble-grumble exercise asks which of `d mumble (b a 5)`, `d (b a 5)`, ...
type-check. In Stitchwort **[measured]**:

- `Nil Nat` is `E-NOT-A-FUNCTION`, "`Nil` takes 0 argument(s)".
- `Nil [a := Nat]` is "`Nil` has no such field ... its parameters have no
  names", and `Cons [a := Bool] …` lists only `(x)` and `(l)`. So a
  constructor's type parameter can't be given at all, except through a
  type annotation, `(Nil: List Nat)`.
- So the mumble-grumble answers differ from the book's (`D Mumble (B A 5)`
  is wrong here, `D (B A 5)` right). The port keeps the seven lines in
  Stitchwort syntax and says the answers aren't the book's.

The book's progression survives for functions (`repeat (a: Type)`,
`repeat''` with `_`, `repeat'''` with `[a: Type]`), but not for
constructors. Allowing `Nil [a := Nat]`, naming a constructor's
parameters after the type's (`type List (a: Type)` gives them `a`), would
cover `@nil nat` and is small; it is the one change here I'd suggest
filing **[estimated]**. Rocq's after-the-fact `Arguments repeat {X}` has
no counterpart and shouldn't get one: implicitness belongs to the header.
That leaves the port's `repeat` explicit where the book's becomes
implicit. No later chapter of Logical Foundations seems to call the
function `repeat` (the matches in Tactics.v to IndProp.v are the tactic
of that name), so it costs nothing yet **[read, by grep]**.

### 5.3 `repl` and `eval` don't load the project

The earlier chapters tell the reader to use `stitchwort repl
src/Sf/Lf/Basics/Basics.sw` and `:t` for the book's `Check`. In `sf/`,
`stitchwort repl src/Sf/Lf/Poly/Poly.sw` and `stitchwort eval
src/Sf/Lf/Poly/Poly.sw '…'` both fail with "there's no namespace
`Sf.Lf.Nat`" for each import **[measured]**: a file given by path is
checked on its own, with only the library (docs/syntax.md, "A file given
by path ... using only the library"). So the README's `repl` line, and
the `:t` advice in Basics.sw and NatList.sw, don't work for any file that
imports another namespace, which is all of them but Nat.sw.

`stitchwort doc Sf.Lf.Poly.combine` does work in the project and prints
the header (`def combine (lx: List a) (ly: List b): List (Prod a b)`), so
this chapter points at `doc`, and at writing a `test` for the book's
`Compute`. The fix is for the REPL and `eval` to find the project from
the current folder, as `check`, `test` and `doc` do. I'd file it as a
bug, and fix the earlier chapters' comments with it; this lane didn't
touch them.

### 5.4 Proofs through an unfinished function pass silently

With `prodUncurry` still `?`, `cases` "proved" `uncurryCurry` and
`curryUncurry`, and so did `rfl`. Two contradictory theorems,
`prodUncurry (x y => x) (Pair True False) = False := rfl` and the same `=
True`, were both accepted, with no message about either **[measured, in
the scratchpad]**. That is documented (docs/syntax.md, Goals: "A use that
has to compute through a `?` ... can't be checked until the goal is
filled, and is unfinished rather than an error"), and `audit` fails them,
so it isn't unsound. But a reader who proves the theorem before writing
the function (the book's order here is define first, but the reader may
not) gets a pass that means nothing, and the summary line says these
declarations are "checked assuming the goals hold", which for these two
can't be so. A note per such declaration ("not checked: `rfl` computes
through `prodUncurry`, which has an open goal") would fix the message;
Lists §5.3's question of using open lemmas is the same area.

### 5.5 Type variables must be lower case

`(X: Type) => …` in a lambda is "unknown name `X`" and `[X := Nat]` a
parse error **[measured]**: capitalised names are types and constructors.
So the book's `X`, `Y`, `Z` are `a`, `b`, `c`, which reads well but makes
`(x: a)` next to `x: X` in the prose a small translation for the reader;
the port says so once.

### 5.6 Small

- **Every definition's type is written.** `Definition ftrue := constfun
  true`, `Definition plus3 := plus 3`, `Definition fold_plus := fold
  plus`, `Definition list123 := …`: each needs `: T` here, and `def x :=
  e` is a parse error that asks for a parameter or a type. `repeat' X x
  count` (no types) is "a parameter needs a type", and `(x: _)` in a
  header is `E-UNSOLVED`, since the header is checked before the body. A
  deliberate design (a header says the type), but the book's "type
  annotation inference" section becomes a paragraph saying why not.
- **`E-UNSOLVED` in a header suggests the wrong fix:** for `def mynil:
  List _ := Nil` it says "supply it explicitly with `f [x := …]`", which
  doesn't apply to a hole in a type.
- **`test` is a keyword,** so the book's `filter (test : X->bool)` can't
  keep its parameter name.
- **A type's parameter can't be implicit:** `type List' [a: Type]` is "a
  type's parameters in brackets must be `auto`", a clear message for the
  book's "a step too far" example.
- **`(x, y)` and `X * Y`** are built in for the library's pair (`Pair a
  b`, `MkPair`), so the book's `prod` is written `Prod a b` and `Pair x y`.

## 6. Generic lemmas that belong in std

Std already has `List.appendNil`, `List.appendAssoc`,
`List.lengthAppend`, `List.reverseAppend`, `List.reverseReverse`,
`List.mapAppend`, `List.mapReverse`, `List.mapId`, `List.mapMap`,
`List.partitionFilters` and `uncurry` **[read]**. Missing, by searching
names and statements under `crates/elab/src/std` **[read]**:

- `List.foldRightLength`: `xs.foldRight 0 (_ n => Succ n) = xs.length`
  (`fold_length_correct`).
- `List.foldRightMap`: `xs.foldRight [] (x acc => [f x, ..acc]) = xs.map
  f` (`fold_map_correct`).
- `List.flatMapAppend`: `(xs ++ ys).flatMap f = xs.flatMap f ++ ys.flatMap
  f` (needed for most proofs about `flat_map`).
- `List.unzipZip` or `List.zipUnzip`: `List.zip ps.unzip.fst
  ps.unzip.snd = ps` (the book's `split`/`combine`, proved in Tactics as
  `combine_split`).
- `curry`, with `uncurryCurry` and `curryUncurry`: std has `uncurry` but
  no `curry` **[read]**.
- `List.filterAppend`, already listed by SW-2836 §6.

## 7. Estimate for the next chapters

This chapter took about 25 minutes from reading to this note, the
scratch solutions included **[measured, by `date`]**, against an
estimate of 3 h. Tactics is next: `apply`, `injection`, `discriminate`,
`unfold`, `generalize dependent`, which are tactic-script ideas, so the
port will be mostly about showing their term-mode counterparts, on
Poly's lists throughout (§5.1). **[estimated]**: 1.5 to
2 h.

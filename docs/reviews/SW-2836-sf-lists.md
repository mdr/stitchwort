# SW-2836: porting Software Foundations, chapter Lists

**Status:** lane report, 11 November 2026. Ports chapter 3 of *Software
Foundations*, Volume 1: *Logical Foundations* (`Lists.v`, "Lists: Working
with Structured Data") to `sf/` as `Sf.Lf.Lists` (D3510), following
[SW-2707](SW-2707-software-foundations-port.md) for Basics and Induction,
with exercises as `?` (SW-2762) on the book's own numbers (SW-2763).

How claims are marked: **[measured]** run today with the release CLI built
from this branch; **[read]** read in the book's sources or this repo;
**[estimated]** my judgement.

## 1. Summary

- **The whole chapter is ported.** Every definition, every worked example
  and theorem the book proves (21 of 21), and every exercise (19, as 48
  statements and 13 functions to write), in the book's order and
  sections. `stitchwort check` in `sf/` passes in about 1.5 s with 138
  open goals (61 of them this chapter's), and `stitchwort test` passes 12
  tests **[measured]**.
- **It ported more cleanly than Basics and Induction.** The book's own
  `natlist` keeps the library's lemmas and automation away from the
  exercises without any special effort: `cases` proves only the two pair
  exercises, and nothing proves the list ones (§4). Every worked proof is
  one or two lines, and the chapter's "stuck" first tries reproduce
  exactly, with the goal Stitchwort prints quoted in place of the book's
  comment (§3.1).
- **What hurts** is notation (§5.1): Stitchwort's list syntax and `++`
  belong to the library's `List`, so the book's `[1;2;3]`, `x :: l` and
  `l1 ++ l2` become `ofList [1, 2, 3]`, `Cons x l` and `app l1 l2`, and
  goals print lists and numbers in full unary. Then two known items from
  SW-2707: a constructor named like its type (`Id`) is still ambiguous,
  and the theorems a reader leaves at `?` can't be used or searched,
  where Rocq's `Admitted` ones can (§5.2, §5.3).
- **I solved every exercise in the scratchpad** (not committed) in a few
  minutes: all went through first time, with no friction worth a
  ticket beyond the imports the reader needs, which the port now provides
  (§4).

## 2. What was ported

| | Lists.v |
|---|---|
| Book: lines, exercises | 1,207, 19 |
| Book: proved theorems (`Qed`) | 21 |
| Port: files, lines | 3, 847 |
| Data types | 6: `NatProd`, `NatList`, `Bag` (a synonym), `NatOption`, `Id`, `PartialMap` |
| Definitions (not exercises) | 16, plus `ofList` (the port's literal helper) |
| Worked theorems | 22: the book's 21 and `mylist1` |
| `Compute` results as tests | 1 |
| Exercises stated | 19: 48 statements, 13 functions |

- **Files.** The book wraps nearly the whole chapter in `Module NatList`
  so that Poly can reuse the names. As in SW-2707, a module is a namespace
  in its own file: `NatList.sw` (`Sf.Lf.Lists.NatList`, pairs to options),
  `Lists.sw` (`Sf.Lf.Lists`, the top level of the Partial Maps section:
  `Id`, `eqbId`) and `PartialMap.sw` (`Sf.Lf.Lists.PartialMap`). The
  README's table gives the reading order, and each file's header says it.
- **Imports.** `From LF Require Export Induction` is `import
  Sf.Lf.Basics (..)` and `import Sf.Lf.Induction (..)`, so a reader has
  `andb`, `eqb`, `odd`, `eqbRefl` and the rest for the exercises without
  editing imports. `Export NatList` in `PartialMap` is `import
  Sf.Lf.Lists.NatList (..)`.
- **Names** as before: `swap_pair` is `swapPair`, `nth_error` is
  `nthError`, `app_length_S` is `appLengthS`, `leb_n_Sn` is `lebNSn`.
  Constructors are capitalised (`Nil`, `Cons`, `Pair`, `Empty`,
  `Record`), and hide the library's in their files, as the book's do.
- **Left out:** `manual_grade_for_add_inc_count` (the grader's), the
  second `fst'`/`snd'` (identical without the notation), and the two
  "ill-formed" definitions, which are a comment quoting the error.
  `add_inc_count` and `bag_count_sum`, where the reader writes the
  statement, are comments with the theorem's name, like Induction's
  informal-proof exercises.

## 3. What ported cleanly, and what came out better

### 3.1 The worked proofs and their first tries

- **Induction on lists is recursion**, as on numbers, and each proof is
  as short as the book's script. `app_assoc`:

  ```
  theorem appAssoc (l1 l2 l3: NatList): app (app l1 l2) l3 = app l1 (app l2 l3) := match l1 with
    | Nil => rfl
    | Cons n l1' => rewrite appAssoc l1' l2 l3 in rfl
  ```

  `rev_length` is `rewrite appLengthS (rev l') n, revLength l' in rfl`,
  the book's two `rewrite`s in one line. `leb_n_Sn`'s inductive case is
  the hypothesis alone (`lebNSn n'`), since the goal computes to it.
- **The stuck first tries reproduce.** The book narrates them in
  comments ("Now we seem to be stuck..."); the port writes the arm as
  `?` and quotes the goal `stitchwort check` printed **[measured]**, so
  the reader sees exactly why the hypothesis doesn't apply:

  ```
  ⊢ Cons n (app (repeat n c') (Cons n (repeat n c'))) = Cons n (repeat n (plus c' (S c')))
  ```

  for `repeat_double_firsttry`, and likewise for `rev_length_firsttry`
  and `app_rev_length_S_firsttry`. `surjective_pairing_stuck` gives
  "`p` and `Pair (fst p) (snd p)` aren't equal".
- **The "multiple patterns versus a pair pattern" warning** gets a clear
  message: `match p with | x, y => x` is "this alternative has 2
  patterns, but the `match` has 1 scrutinee" **[measured]**.

### 3.2 Better than Rocq

- **Record eta.** Declared as a record, `type NatProd = { n1: Nat, n2:
  Nat }`, the book's `surjective_pairing_stuck` holds by `rfl`
  **[measured]**. The port keeps the data type, to follow the book's
  lesson about `destruct`, and says so in a sentence.
- **Separate files need no build step**, as in Induction: the three
  namespaces check in dependency order from one `stitchwort check`.
- **`rewrite` without arguments did the right thing** in the scratch
  solution of `app_assoc4`: `rewrite appAssoc, appAssoc in rfl` closed it
  **[measured]**, where the book warns that the short solution needs
  care.

## 4. The exercises

The chapter's exercises are about the book's own `NatList`, so the
library's list lemmas (`List.appendNil`, `List.reverseReverse`, ...) can't
be used on them, and the automation does little **[measured]**, by trying
`cases` on each of the 11 statements that don't depend on a function the
reader writes:

- `cases` proves `sndFstIsSwap` and `fstSwapIsSnd` (one `match` on a
  pair; the book's proofs are that too).
- It doesn't prove `appNilR`, `revAppDistr`, `revInvolutive`,
  `appAssoc4`, `involutionInjective`, `revInjective` ("found nothing to
  split on": it doesn't take recursive types apart, so it does no
  induction), or `eqbIdRefl` (§5.5).
- The tests of the functions the reader writes (`testNonzeros`, ...) are
  `rfl` once the function is written, as the book says.

I solved all of them in a scratch copy of `sf/`, nothing of which is
committed or quoted here: a few minutes, every proof first time. Two
things a reader would meet:

- **Imports.** My first solution of `eqblist` failed with "unknown name
  `andb`", and `updateEq` with "unknown name `eqbIdRefl`": the files
  imported only what the worked proofs use. They now import whole
  namespaces, as the book's `Export` does.
- **`eqblistRefl` needs Induction's `eqbRefl`**, an exercise. Until the
  reader proves it, anything using it is "not checked" (§5.3). That
  matches the book's ordering, but in Rocq an `Admitted` `eqb_refl` can
  be used straight away.

## 5. Friction, ranked by how much it hurts a reader

### 5.1 No notation for the book's lists

The book introduces `x :: l`, `[ ]`, `[x; ..; y]` and `++` for its
`natlist`, and uses them on nearly every line after. In Stitchwort the
list brackets and `++` are syntax that always means the library's `List`
(docs/syntax.md: "Syntax always means the library's"), and there is no
`Notation` (D1200). So **[read, measured]**:

| Book | Port |
|---|---|
| `[1;2;3] ++ [4;5] = [1;2;3;4;5]` | `app (ofList [1, 2, 3]) (ofList [4, 5]) = ofList [1, 2, 3, 4, 5]` |
| `h :: t` (pattern and expression) | `Cons h t` |
| `rev t ++ [h]` | `app (rev t) (Cons h Nil)` |
| `hd 0 [1;2;3] = 1` | `hd O (ofList [1, 2, 3]) = S O` |

`ofList` is the port's own conversion (a library list of library numbers
to a `NatList`), defined in the file and explained where the book
introduces its notation. It computes, so `rfl` sees through it. It keeps
the test examples readable; statements and patterns use the constructors.

The other half of the cost is in **goals and messages**, which print the
computed form: the goal of `testHdError3` is

```
⊢ hdError (Cons (S (S (S (S (S O))))) (Cons (S (S (S (S (S (S O)))))) Nil)) = Some (S (S (S (S (S O)))))
```

where Rocq prints `hd_error [5; 6] = Some 5`. For the book's own `nat`
Rocq has a number notation; Stitchwort has nothing to print `S (S O)` as
`2` for a type other than its own `Nat`.

**Options.** (a) Accept it, as here: Poly moves to polymorphic lists, and
the port could use the library's `List` from Poly on, with the cost that
its lemmas give exercises away (SW-2707 §6 item 2). (b) Let list literals
and `[x, ..xs]` patterns elaborate to any type whose constructors are a
nil and a cons, chosen by the expected type, as Lean's `[a, b]` is
generic through a type class, and print such values back as literals.
Language-visible and Matt's decision; it would also serve user types like
`NonEmptyList`. (c) A display-only fix: print a closed `S (S O)`-shaped
term of any unary type as a numeral, and a closed `Cons`/`Nil` chain as a
list, in goals. Smaller, but it affects every message, so also Matt's
call. I'd lean to (a) for the port and take (b) only if users ask for
literal syntax on their own list-like types.

### 5.2 A constructor named like its type is still ambiguous

The book's `Inductive id := Id (n : nat)`, written as `type Id = | Id (n:
Nat)`, makes `(x1 x2: Id)` in the next definition `E-AMBIGUOUS`: "`Id`
could mean `…Id` or `…Id.Id`" **[measured]**. The same as SW-2707 §6
item 8 (`Grade`); the port names it `MkId`. Later chapters do this often
(Imp's and Maps' types). The fix proposed there still stands: in a type
position, prefer the type.

### 5.3 A reader's unproved lemmas can't be used or found

In Rocq a reader who admits `add_comm` can still use it, and `Search (?x
+ ?y = ?y + ?x)` finds it (the book's own example). Here, a theorem with
`?` is open: what uses it isn't checked, and `stitchwort search` doesn't
list it. Run in `sf/`, `stitchwort search 'plus ?x ?y = plus ?y ?x'`
listed six results, none of them Induction's `addComm` (still `?` in the
port), and took 40 s wall-clock, 16.5 s of CPU **[measured, once]**. The
port's Search section says both. Two separate gaps:

- **Search skips open declarations.** For a textbook, an open theorem is
  still a statement worth finding; listing it marked "open" would match
  Rocq. Small, and probably uncontroversial.
- **Using an open lemma.** SW-2707's item 1 (answered by `open-goals:
  warn`) covers checking a project with holes, but a proof that cites an
  open lemma is still not checked. Rocq checks it against the admitted
  statement. Checking it as if the lemma were an assumption (and
  reporting it as resting on that assumption, as `audit` already does)
  would let a reader do exercises out of order, as the book's grading
  allows. Matt's decision (trust).

### 5.4 Search is slow on a small project

40 s for a project of 10 namespaces (above), most of it loading and
comparing against the library. SW-2707 measured 18 s for `search --at`.
The book tells the reader to use `Search` constantly. Not a port issue;
a performance finding for `search`.

### 5.5 `cases` on `eqbIdRefl`

`cases` on `eqbId x x = True` split the Boolean result of `eqbId x x`
and reported "can't close the case `eqbId x x = False`", instead of
splitting `x` (an `Id`, one constructor) and then failing on `eqb n n`
**[measured]**. The same shape as SW-2707's item 10 (it splits a stuck
call's result before the variable under it). Harmless for SF, since the
exercise is meant to be done by hand, but the message is misleading:
the reader may think the statement is false.

### 5.6 Small

- **`Check` and `Compute`** (1 and 2 uses) as before: `Compute` becomes a
  test (the second, `fst (3,5)`, is the notation and goes), and `Check`
  a comment pointing at the REPL's `:t`.
- **`Definition` versus `Fixpoint`.** The book gives `countoddmembers` a
  `Definition` header as a hint not to recurse. Stitchwort has one
  `def`, so the hint is a sentence.
- **`sum : bag -> bag -> bag`** with unnamed arguments ports exactly
  (`def sum: Bag → Bag → Bag := ?`), and the hint still makes sense.

## 6. Generic lemmas that belong in std

The chapter's theorems about `natlist` are, generalised, facts about the
library's `List`. Std already has `List.appendNil`, `List.appendAssoc`,
`List.lengthAppend`, `List.lengthSnoc`, `List.reverseAppend`,
`List.reverseReverse`, `List.lengthReverse`, `List.countAppend` and
`List.lengthReplicate` **[read]**. Missing, by searching the theorem names
and statements under `crates/elab/src/std` **[read]**:

- `List.replicateAdd`: `List.replicate (m + n) x = List.replicate m x ++
  List.replicate n x` (the book's `repeat_plus`).
- `List.reverseInjective`: `xs.reverse = ys.reverse → xs = ys`
  (`rev_injective`).
- `List.filterAppend`: `(xs ++ ys).filter p = xs.filter p ++ ys.filter
  p` (`nonzeros_app`, generalised; std has `List.filterMapAppend` only).
- `List.headOrHead`, or similar: `xs.headOr d` equals `List.head xs`
  with `d` as the default (`option_elim_hd`).
- An injectivity lemma for involutions, `(∀ x => f (f x) = x) → f x = f y
  → x = y` (`involution_injective`); std has no namespace for facts about
  functions in general, so where it goes is part of the question.

## 7. Estimate for the next chapters

This chapter took about 15 minutes in all, from reading it to this
note, solving the exercises in the scratchpad included **[measured, by
`date`]**, against SW-2707's estimate of 1.5 h. Poly is next: polymorphic
lists, options and pairs, `Arguments`/implicit arguments (Stitchwort
infers them too), and higher-order functions. Its main question is §5.1's
option (a): whether the port's lists become the library's `List`, which
brings back literal syntax and loses the exercises to std's lemmas, or
stay the book's own type. **[estimated]**: 1 to 1.5 h for Poly either way.

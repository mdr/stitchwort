# Software Foundations in Stitchwort

A port of the first three chapters of *Software Foundations*, Volume 1:
*Logical Foundations* (Basics, Induction and Lists), from the book's Rocq sources
to Stitchwort. The book's prose is kept as comments, its definitions and
worked proofs are translated, and its exercises are stated but not solved.
Copyright and licence: [LICENSE-SF](LICENSE-SF).

| Chapter | Namespace | Files |
|---|---|---|
| Basics.v | `Sf.Lf.Basics` | `src/Sf/Lf/Basics/Basics.sw`, with the book's modules as namespaces beside it: `Playground`, `TuplePlayground`, `LateDays`; `NatPlayground` and `NatPlayground2` are `src/Sf/Lf/Nat.sw` (below); `Library.sw` proves the two library lemmas the chapter quotes |
| Induction.v | `Sf.Lf.Induction` | `src/Sf/Lf/Induction/Induction.sw` |
| Lists.v | `Sf.Lf.Lists` | `src/Sf/Lf/Lists/NatList.sw` first: the book's module `NatList`, which is most of the chapter (`Sf.Lf.Lists.NatList`); then `Lists.sw`, the Partial Maps section's `Id`; then `PartialMap.sw`, its module `PartialMap` |

**The book's own numbers.** The chapters work on the numbers of
`src/Sf/Lf/Nat.sw` (`Sf.Lf.Nat`): the type `Nat` with constructors `O` and
`S`, and `plus`, `mult` and `minus`, as the book's `NatPlayground` and
`NatPlayground2` define them, with no lemmas. Booleans, and the book's
`andb`, `orb`, `eqb`, `leb`, are the library's `Bool` and functions of the
port's own. The reason is that the library's `Nat` has a large stock of
proved facts (`Nat.addComm`, `Nat.mulZero`, ...), decision procedures
(`omega`, `ring`, `cases`) and an addition that computes on its second
argument, and between them they solve many exercises in one word; the book
keeps these out of the reader's way and so does the port. Costs: number
literals stand for the library's `Nat` only, so `3` is written `ofNat 3`
(a function that computes to `S (S (S O))`; `O` and `S O` are written as
they are), and the operators `+ * - <=` aren't available, so call `plus`,
`mult`, `minus`, `leb` by name. The `LateDays` module (grades, and
`lateDays: Nat` with `<`) still uses the library's `Nat`: its exercises
are about the policy, not about numbers.

**The book's own lists.** Lists defines `NatList` with constructors `Nil`
and `Cons`, and `app`, `rev`, `length` and the rest, as the book does.
Stitchwort's list syntax (`[1, 2, 3]`, `[x, ..l]`) and `++` always mean
the library's `List`, so they don't apply to `NatList`: `app` is called by
name, and a list of numbers is written `ofList [1, 2, 3]`, which converts
a library list as `ofNat` converts a number. The library's list lemmas and
automation don't reach `NatList`: of the chapter's exercises, `cases`
proves only the two about pairs (`sndFstIsSwap`, `fstSwapIsSnd`), and
`rfl` the tests of the functions you write, as the book intends.

**Which exercises the library solves.** On the library's `Nat` (so not
on the port's), measured by trying `rfl`, `omega`, `ring` and `cases` on
each exercise's statement:

- *`omega` or `cases` prove them outright:* `plusIdExercise`, `multN1`,
  `mul0R`, `plusNSm`, `addComm`, `addAssoc`, `addShuffle3`, `mulComm`,
  `mult1L`, `zeroNbeqPlus1`, `zeroNeqbS`, `sNeqb0`, `doubleIncr`. (`ring`
  proves the multiplication ones too, and also `multPlusDistrR` and
  `multAssoc`, which `omega` can't.)
- *`rfl` proves them, because the library's `+` computes on its second
  argument:* `plusNSm`, `mult1L`, `zeroNbeqPlus1`, `zeroNeqbS`,
  `sNeqb0`, `doubleIncr`, and the chapter's own `plus1Neq0FirstTry` and
  `n + 0 = n`, the book's examples of computing getting stuck.
- *`cases` proves the Boolean ones:* `andbTrueElim2`, `andbEqOrb`,
  `andbFalseR`, `all3Spec`. These are on the library's `Bool` here too,
  since the book's proofs of them are case analysis anyway, and `cases` is
  the same work done for you.
- *Not solved by any of them:* `doublePlus`, `eqbRefl`, `evenS`, `lebRefl`
  and `identityFnAppliedTwice` need induction or a hand proof, and the
  `Bin` exercises are definitions and proofs about them.

Doing the exercises by hand is the point; use these only to see what the
tools do.

Read the files in the book's order: Basics.sw says where each module's file
comes in.

```sh
stitchwort check      # every definition and worked proof; a warning per exercise left
stitchwort test       # the `Compute` examples, written as tests
stitchwort repl src/Sf/Lf/Basics/Basics.sw   # evaluate, and `:t` for types
```

**Exercises.** An exercise is its statement with `?` where your work
goes: `theorem plusIdExercise (n m o: Nat) (h1: n = m) (h2: m = o): n + m =
m + o := ?` is for you to prove, and `def nandb (b1: Bool) (b2: Bool): Bool
:= ?` is for you to write. The project's `stitchwort.yaml` says
`check: open-goals: warn`, so `stitchwort check` reports each `?` as a
warning with its goal and still passes; fill one in and its warning goes.
`stitchwort audit` fails every theorem that still rests on a `?`, and
`stitchwort test` fails while a test uses an unfinished function. The
book's authors ask that solutions not be posted publicly, so please keep
yours out of public repositories.

What was easy and hard to port, and what Stitchwort could change, is in
[docs/reviews/SW-2707-software-foundations-port.md](../docs/reviews/SW-2707-software-foundations-port.md)
(Basics, Induction) and
[docs/reviews/SW-2836-sf-lists.md](../docs/reviews/SW-2836-sf-lists.md)
(Lists).

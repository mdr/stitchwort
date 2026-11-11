# Software Foundations in Stitchwort

A port of the first two chapters of *Software Foundations*, Volume 1:
*Logical Foundations* (Basics and Induction), from the book's Rocq sources
to Stitchwort. The book's prose is kept as comments, its definitions and
worked proofs are translated, and its exercises are stated but not solved.
Copyright and licence: [LICENSE-SF](LICENSE-SF).

| Chapter | Namespace | Files |
|---|---|---|
| Basics.v | `Sf.Lf.Basics` | `src/Sf/Lf/Basics/Basics.sw`, with the book's modules as namespaces beside it: `Playground`, `TuplePlayground`, `NatPlayground`, `NatPlayground2`, `LateDays` |
| Induction.v | `Sf.Lf.Induction` | `src/Sf/Lf/Induction/Induction.sw` |

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
[docs/reviews/SW-2707-software-foundations-port.md](../docs/reviews/SW-2707-software-foundations-port.md).

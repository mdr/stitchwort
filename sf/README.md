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
stitchwort check      # every definition and worked proof
stitchwort test       # the `Compute` examples, written as tests
stitchwort repl src/Sf/Lf/Basics/Basics.sw   # evaluate, and `:t` for types
```

**Exercises.** A theorem to prove is stated as a definition of a `Prop`
(`def plusIdExercise: Prop := ∀ (n m o: Nat) => …`): to do it, write a
`theorem` with that statement and a proof. A function to write has a
placeholder body marked "Exercise", which is not the answer. The book's
authors ask that solutions not be posted publicly, so please keep yours
out of public repositories.

What was easy and hard to port, and what Stitchwort could change, is in
[docs/reviews/SW-2707-software-foundations-port.md](../docs/reviews/SW-2707-software-foundations-port.md).

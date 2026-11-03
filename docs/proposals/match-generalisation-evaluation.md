# Generalising a `match` scrutinee: what to evaluate

SW-1096, 3 Nov 2026 (D2229). A short survey, then how Stitchwort compares
and what SW-1096 changes. Marked **[fetched]** where checked against the
source or docs on 3 Nov, **[memory]** where it couldn't be (on a train).

## The problem

To build a dependent `match`'s motive, the elaborator looks for the
scrutinee `e` in the goal and the hypotheses' types and abstracts it.
Stitchwort compares normal forms: it evaluates `e` and reads it back
(`matching::normals`), then looks for that term, syntactically, in the goal
and types as read back. When `e` is a long computation, such as
`C.run (() => loop 1000000 0) 0` in `main`, the elaborator runs it at check
time in `core::value`, which has no handler fusion or tail resumption:
`check` peaked at 7.36 GB and took 17 s (SW-1096's diagnosis).

## What others do

- **Lean 4.** `elabDiscrs` in `Lean/Elab/Match.lean` abstracts each
  discriminant with `kabstract matchType discr`. The discriminant is only
  `instantiateMVars`'d, never put in whnf or normal form **[fetched]**.
  `kabstract` (`Lean/Meta/KAbstract.lean`) visits the expected type and
  calls `isDefEq` only on closed subterms whose head symbol and argument
  count match the pattern's (`toHeadIndex`, `headNumArgs`) **[fetched]**.
  So the expensive check runs only on syntactically plausible candidates,
  and the discriminant is never run. `generalizing := false` turns off
  generalisation in the hypotheses ([reference: pattern
  matching](https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching),
  [KAbstract.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean),
  [Match.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Match.lean)).
- **Rocq/Coq.** A `match` with no `return` clause takes its predicate from
  the expected type by abstracting the term's occurrences, or else uses a
  non-dependent one. `destruct`, `case_eq` and `generalize` abstract
  occurrences by matching subterms up to syntactic equality modulo evars,
  with a head key, not up to conversion. Neither normalises the term
  **[memory]**. Otherwise the user writes `as … in … return` by hand.
- **Agda.** `with`-abstraction normalises both the with-expression and the
  goal and argument types, then abstracts syntactically: "X ≃ Y" is
  "equality of the normal forms of X and Y". Only occurrences visible at
  abstraction time are generalised **[fetched]**
  ([with-abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html)).
  Stitchwort's design is Agda's. The cost of normalising a big
  with-expression is a known Agda complaint **[memory]**.
- **Idris 2.** `with` normalises the with-value (`nf`) and replaces subterms
  of the normalised goal that are *convertible* with it (`replace`, in the
  clause elaborator) **[memory]**. It is close to Agda's design and pays
  the same cost.

So the systems fall into two groups. Lean and Rocq never evaluate the
scrutinee: they match occurrences up to syntax, with a head-symbol filter in
front of a definitional-equality check. Agda and Idris 2 normalise, and
evaluating something expensive at elaboration time is the price they pay
for finding occurrences that differ from the source only by computation.

## Stitchwort

Stitchwort is in the Agda group, on purpose: W-MATCH-NOT-FOUND's note says
"the search compares what terms compute to". Proofs rely on this when the
goal shows the computed form of a call written unreduced in the `match`.
Moving to Lean's approach (no evaluation, head-keyed matching up to
definitional equality on candidates) would change which programs check: a
match that today finds its scrutinee only after both sides compute might
not find it. That is a language decision for Matt, not this lane's, and I
don't recommend it now: the cost only matters for long computations, and a
cheap test removes most of it.

**SW-1096's fix** keeps the design. Before evaluating a single scrutinee,
`normals` asks whether its normal form could occur in the goal or
hypotheses at all, by looking at their syntax (`matching::cannot_occur`).
Suppose the scrutinee's type is a data type `D`, so its normal form `n` is
not a type, a sort, a function or a redex. Suppose also that the targets
(the goal, the hypotheses' types and the scrutinee's type, as read back) are
built only from variables, data types, sorts, Π, λ, application, `=`,
annotations and definitions whose types end in a sort or in a data type
other than `D`. Then a subterm of a target equal to `n` would have to be
headed by a variable free in both, since a definition's application has
the wrong type. There is no such variable if the scrutinee has no free
variables or unknowns, or if the targets have no free variables. So `n`
occurs nowhere, and `normals` answers "too big to occur" (`None`) without
evaluating, as its size cap already does. The outcome is the same as
today's for every program: the occurrence test would have found nothing.
The only differences are that a scrutinee whose evaluation ran out of
resources now checks, and that W-MATCH-NOT-FOUND shows the scrutinee as
written. `main`'s goal `{IO} ()` passes: its effect row holds definitions,
but none whose type ends in the scrutinee's data type.

This is a filter in Lean's spirit (look at the targets' heads before doing
anything expensive), applied in front of Agda's comparison. It covers the
case that hurts, a `match` in `main` on a handled computation, whose goal is
`{IO} ()`. It doesn't help when the goal mentions a constructor or number of
any type: then the scrutinee is still evaluated. A finer filter (only the
scrutinee type's own constructors, plus the heads a stuck normal form could
have) or a work budget could follow if that case shows up. Fusion and tail
resumption in `core::value` would lower the cost of whatever is still
evaluated.

**Measured** (`/usr/bin/time -l`, second run with a warm cache, load
average 16-27 from other lanes): `check cn1m.sw` (a million handled
operations) went from 4.7-7.4 GB and 17-26 s to 69 MB and 0.16 s. `check
next.sw` (`Parse.run` over 160,000 characters) went from 1.35 GB and 5-6 s
to 395 MB and 0.6 s. What next.sw has left, about 1.9 KB a character, isn't
the scrutinee. A sampled profile puts it in the case split: `check::substitute_in` reads back and
re-evaluates every value in the context, including `let input := …`'s
160,000-element list. The helper form avoids it
(103 MB), since the helper's context holds only its parameter.

# Proposal: number patterns without `Succ` chains

**Status:** proposed, 15 October 2026, for external review. Not implemented.

This note is meant to be read without knowing the codebase. The first section
describes the parts of Stitchwort it touches.

## Background: the parts of Stitchwort involved

Stitchwort is a small, strict, pure, total, dependently typed language. Its
trusted kernel checks a small core language; an elaborator turns the surface
language into it.

- **Numbers.** `Nat` is defined in the prelude as `Zero | Succ Nat`, and that
  is what it means. A number is *stored* compactly, as one arbitrary-precision
  value, which behaves exactly like its chain of `Succ`s: matching on `5`
  takes the `Succ` branch with field `4`, and conversion treats `3` and
  `Succ 2` as equal. A number with an unknown inside, `Succ (Succ x)` or
  `k + x`, is kept as "`k` `Succ`s around `x`". A few prelude functions run
  natively on numbers (`add`, `eqNat`, `decEqNat : (m n : Nat) -> Decidable
  (m = n)`, …), and are trusted ([native numbers](native-numbers.md)).
- **Data types have no indices** (only parameters). A "vector of length `n`"
  is a function computing a type from `n`, so dependent types over numbers
  come from computation.
- **Definitions are case trees.** Equations compile (by the usual
  pattern-matrix method) to nested `case` nodes, each on one variable, with
  one branch per constructor. The kernel allows `case` *only* at the top of a
  definition's body and at the top of each branch, never inside an
  expression. In each branch, the kernel substitutes the constructor value
  for the matched variable throughout the context and the goal (that's how a
  branch learns `n = Succ m`).
- **Unfolding.** A definition applied to all its arguments unfolds only if
  its case tree can take a step; otherwise it stays folded (`length xs` with
  unknown `xs` stays `length xs`). This keeps conversion terminating.
- **Totality.** Exhaustiveness is checked by the elaborator and re-checked
  by the kernel (one branch per constructor). Termination is structural: a
  recursive call must pass, in some fixed position, a variable bound by a
  `case` on that parameter (or something matched out of it).
- **Extraction.** Checked programs compile to JavaScript; `Nat` is `bigint`.

## The problem

A number pattern is compiled as that many nested `Succ` patterns: `f 404 = …`
becomes `f (Succ (Succ … (Succ Zero)))`, 404 deep, so 405 nested `case`s.

- **A cap.** Patterns above 256 are refused, so a realistic program like this
  doesn't compile:

  ```
  statusText : Nat -> Text
  statusText 200 = "OK"
  statusText 404 = "Not Found"
  statusText 503 = "Service Unavailable"
  statusText _   = "Unknown"
  ```

  ```
  [E-UNSUPPORTED] Error: number patterns above 256 aren't supported
  ```

- **Checking is slow below the cap.** Each `case` level rewrites the whole
  context and goal, and the context grows by one variable per level, so the
  cost grows roughly with the cube of the largest number. Measured with the
  release build of the command-line checker on an Apple-silicon Mac, for
  `f N = True; f _ = False`:

  | program | time | peak memory |
  |---|---|---|
  | `f 100` | 0.15 s | 22 MB |
  | `f 200` | 0.97 s | 121 MB |
  | `f 256` | 1.99 s | 242 MB |
  | a table `f 0 = 0` … `f 255 = 255`, `f _ = 0` | 1.99 s | 243 MB |

  A sampling profile of `f 256` put about three quarters of the time in the
  elaborator's checking of the case tree and a quarter in the kernel's
  re-check of the same `case`s; building the tree itself was negligible.

## What other languages do

- **Haskell, OCaml.** No dependent types, so a literal pattern is only a
  test. GHC desugars an overloaded literal pattern to an equality test using
  the type's `Eq`; OCaml compiles integer and string patterns to comparisons
  or jump tables. The classic algorithm (Maranget 2008) treats a column of
  literals like a constructor column with infinitely many constructors: one
  branch per literal that appears, plus a default.
- **Lean 4.** A `Nat` literal pattern is turned into a *value* pattern, and
  the match compiler handles value patterns with `caseValues`, which splits a
  goal `C x` into one subgoal per listed value plus a catch-all, requires
  decidable equality on the type, gives each value's subgoal a hypothesis
  `x = v` and substitutes it, and gives the catch-all nothing (or the
  inequalities). This all happens in the elaborator, with Lean's general
  `subst`/`casesOn` machinery; the kernel never sees a literal pattern, and
  the code generator compiles the test to a native comparison.
- **Agda.** Its internal case trees (`CompiledClauses`) have a `Case` node
  with constructor branches, a map from *literal* to subtree
  (`litBranches`), and a catch-all branch. Separately, the type checker has
  `expandLitPattern`, which rewrites a natural-number literal pattern into
  `suc`/`zero` patterns and refuses literals above 20 with "Matching on
  natural number literals is done by expanding the literal to the
  corresponding constructor pattern, so you probably don't want to do it
  this way." We didn't establish exactly when each path is taken (our
  reading: literal branches for a column of literals, expansion when a
  literal must be checked against constructor patterns).
- **Idris 2.** Case trees branch only on variables, with alternatives for
  constructors, `ConstCase` for a literal of a primitive type, and a
  `DefaultCase`. `Nat` is a Peano type that's represented as an integer at
  runtime; we haven't confirmed how a `Nat` literal *pattern* is checked.
- **Rocq.** `nat` numerals are notation for `S (S … O)`, so a numeral
  pattern is a chain of constructor patterns, like Stitchwort today (not
  re-checked for this note).

So there are two families: literal tests handled entirely in the elaborator
using decidable equality and rewriting (Lean), and a literal-switch node in
the case-tree language with a default branch (Agda's `litBranches`, Idris's
`ConstCase`).

## Options

### A. Elaborate to existing terms (Lean's approach)

Compile a number test to `elimDec (decEqNat n 404) (\h -> yes) (\h -> no)`,
where `elimDec : Decidable p -> (p -> a) -> (Not p -> a) -> a`. The kernel
already checks all of this, and `decEqNat` runs natively, so a test is one
step.

No new kernel feature, but it fits Stitchwort's kernel poorly:

- **`case` may only appear at the top of a definition.** A test written as a
  function application isn't at the top, so nothing below it may be a
  `case`. Every constructor split would have to be made before any number
  test: a second, reordered compilation strategy.
- **The matched branch has to learn `n = 404` from `h`.** For a goal that
  mentions `n` (`f : (n : Nat) -> Vec n Bool`), the branch's value must be
  transported along `h` with `J`, and so must every argument whose type
  mentions `n` ("generalise, then rewrite"). Lean has tactics for this;
  Stitchwort's elaborator would need it written by hand, including
  replacing `n` by `404` inside the branch's elaborated term.
- **Definitions would unfold differently.** A test inside an application
  isn't a case-tree step, so `statusText n` with unknown `n` would unfold to
  a chain of stuck `elimDec`s, in error messages and in conversion, where
  today it stays `statusText n`.
- **The JavaScript would allocate** a `Decidable` object and two closures
  per test, unless the JS backend learned to recognise the shape.

### B. A number switch in the case tree (Agda's / Idris's approach) — recommended

Add one node to the kernel's case trees:

```
NumCase(n, [(200, b₁), (404, b₂), …], default)
```

"If variable `n` is 200, take `b₁`; if it's 404, take `b₂`; …; otherwise
take `default`." The numbers are listed in increasing order, without
repeats. Like `case`, it's only allowed in case-tree positions.

- **Checking.** `n` must have type `Nat`. Each listed branch is checked with
  `n` replaced by its number throughout the context and the goal, exactly
  as a `case` branch replaces `n` by `Succ m`. So in the `404` branch the
  goal `Vec n Bool` is `Vec 404 Bool`, and `rfl : n = 404` checks. The
  default branch is checked with nothing new known. One rewrite per listed
  number, over a context that doesn't grow: linear, not cubic.
- **Evaluation.** If `n` is a number, pick its branch (or the default). If
  `n` is `k + x` with `x` unknown and every listed number is below `k`, `n`
  can't be any of them: take the default. Otherwise the tree is stuck, and
  the definition stays folded, as with a `case` on an unknown.
- **Elaboration.** In the pattern matrix, a column whose patterns are
  numbers, variables and `_`, with no `Zero`/`Succ` constructor pattern,
  compiles to a `NumCase` (Maranget's literal column): the `404` branch
  keeps the rows with `404`, a variable or `_` there; the default keeps the
  rows with a variable or `_`. A column that mixes numbers with
  `Zero`/`Succ` patterns (`half 0`, `half 1`, `half (Succ (Succ n))`)
  compiles exactly as today: a `case`, where a number `k` in the `Succ`
  branch becomes `k - 1` on the field. That peels only as many levels as the
  source writes `Succ`s, so the cap can go.
- **JavaScript.** `switch (n) { case 200n: … case 404n: … }` then the
  default: native `bigint` comparison, no allocation.

### C. Keep `Succ` chains but make them cheaper

Share work between levels, or skip re-substituting variables that can't
mention the scrutinee. This could lower the constant and maybe the exponent,
but a pattern `10^30` still can't be a chain, and the tree is still
proportional to the number. Rejected.

## Why B is sound

A `NumCase` is shorthand for something the kernel already accepts: nested
`case`s on `Zero`/`Succ` (the `Succ` chain) whose leaves at the listed
numbers are the listed branches and whose every other leaf is a copy of the
default. Compare the two rules:

- **Listed branches:** identical. In both, `n` is replaced by the number
  throughout the context and goal (the chain does it one `Succ` at a time).
- **Default:** the chain's copies of the default are each checked knowing a
  little about `n` ("`n` is `Zero`", "`n` is `Succ (Succ m)`", …).
  `NumCase` checks the default once, knowing nothing. Any default that
  checks with less information also checks with more, so every `NumCase`
  the kernel accepts corresponds to a chain it would accept. The rule is
  weaker, never stronger.
- **Evaluation agrees.** On a number, both pick the same branch. On
  `k + x`, the chain peels `k` `Succ`s and then needs to look at `x` unless
  every listed number is below `k`, in which case it reaches a default leaf;
  `NumCase` takes the default in exactly that case and is otherwise stuck.
  So conversion gives the same answers, and so does type checking.
- **Exhaustiveness.** A `NumCase` always has a default, so it's exhaustive
  by construction. The elaborator reports a column of only numbers with no
  variable or `_` row as `E-NONEXHAUSTIVE` (listing the numbers it handles);
  the kernel would treat a missing default as a malformed term.
- **Termination.** A `NumCase` binds no variables, so the structural
  termination checker learns nothing from it, and it can't make a recursive
  call look smaller. Recursion through `f (Succ n) = … f n …` still goes
  through a `case`, as today, so it's accepted exactly where it is now, and
  the existing must-reject examples (rebuilding the matched value, as in
  `loop (Succ n) = loop (Succ n)`) stay rejected.
- **Trusted code.** The kernel rule and the branch choice in the evaluator
  are new trusted code, roughly 100 lines. A second, deliberately
  independent reference evaluator already exists for differential testing;
  it would get its own implementation of the branch choice (a linear scan
  where the main one uses binary search), and the existing kernel fuzzer
  could generate `NumCase` nodes.

## Interactions

- **Dependent result types.** Because the kernel substitutes the number, the
  `404` branch knows `n = 404` by computation, without a proof object:
  `f : (n : Nat) -> Vec n Bool` with `f 3 = [True, True, True]` checks as it
  does today.
- **Mixing numbers, `Zero`/`Succ` and variables in one column.** Any
  `Zero`/`Succ` pattern in the column means a `case` split (today's
  behaviour); otherwise a `NumCase`. A variable row belongs to every branch,
  with the variable naming `n`.
- **Several columns, first match wins.** Row order is kept in every branch;
  later columns are compiled in each branch as usual, so `g 404 True = …`
  followed by `g n b = …` works. A column chosen for a `NumCase` contains
  only variables and `_` afterwards, so compilation terminates.
- **Behaviour change for small numbers.** `f 0 = …; f n = …` becomes a
  `NumCase` instead of a `case`. It computes the same on numbers and on
  `Succ x` (which takes the default, as before). What it loses: inside the
  default, nothing is known about `n`, where today it's known to be
  `Succ m`. That matters only if something there depends on it, for example
  an absurd pattern `()` on a proof of `IsZero n` in another column. Writing
  `f (Succ m)` instead of `f n` restores today's behaviour. Nothing in the
  repository's examples or prelude relies on it: the prelude's `isSpaceCode`
  and `digitChar` use only numbers and `_`, and `half`, `fib` and `peel`
  mix in `Succ` patterns, so they keep the `case` split.
- **Text and characters.** There are no `Char` or `Text` literal patterns
  today. A `Char` pattern `'a'` could later be sugar for `MkChar 97 _` (a
  `Char` is its code plus a proof that the code is valid), which this design
  already compiles well: a `case` on `MkChar`, then a `NumCase` on the code.
  A `Text` pattern would be a `case` on the text's list of characters, one
  character at a time, so linear in its length. Neither is part of this
  change.

## Open questions for the reviewer

1. **Kernel feature or not?** B adds a node to the kernel's case trees
   (about 100 trusted lines) to avoid the elaborator-side transport of
   option A. Is the soundness argument above (a `NumCase` is a weakened
   `Succ` chain) convincing enough to justify the new trusted code, or would
   you rather pay A's costs to keep the kernel unchanged?
2. **Should the default branch learn anything?** Lean's catch-all can carry
   `x ≠ v` hypotheses. B gives the default nothing. Is there a reasonable
   program where that matters enough to bind a proof of `Not (n = 404)` in
   the default (which would need a name in the surface syntax)?
3. **The behaviour change for `f 0 = …; f n = …`.** Is losing "`n` is
   `Succ m`" in the default acceptable, or should a column whose numbers
   are all small (say, at most 1) keep the `case` split for compatibility?
   That would mean two compilation rules for the same syntax.
4. **Choosing between `case` and `NumCase` per column.** The rule is "any
   `Zero`/`Succ` pattern in the column forces a `case`". With
   `f 404 = …; f (Succ n) = …; f 0 = …`, that peels one level, and the
   `Succ` branch's `403` becomes a `NumCase` on the predecessor. Is there a
   better rule, for example splitting `case` only where the first row has a
   constructor?
5. **Evaluation on `k + x`.** B takes the default when every listed number
   is below `k`, matching the chain. Any concern that this makes conversion
   behave differently from the chain in a case we haven't thought of (for
   example with metavariables during unification)?

## Sources

- L. Maranget, *Compiling Pattern Matching to Good Decision Trees*, ML
  Workshop 2008, pp. 35–46 (constants are handled as constructors of a type
  whose signature is never complete, so a default matrix is always needed).
  <https://doi.org/10.1145/1411304.1411311>
- J. Cockx and A. Abel, *Elaborating Dependent (Co)pattern Matching*,
  ICFP 2018 (case trees for a dependently typed core, as in Agda).
  <https://dl.acm.org/doi/10.1145/3236770>
- Lean 4 API, `Lean.Meta.caseValues` ("Split goal `... |- C x` … into
  `values.size + 1` subgoals … The type of `x` must have decidable
  equality … the last subgoal is for the "else" catchall case").
  <https://lean-lang.org/doc/api/Lean/Meta/Match/CaseValues.html>
- Lean 4 API, `Lean.Meta.Match.Value` (`isMatchValue`: "a term that should
  be processed by the `match`-compiler using `casesValues`").
  <https://www.cs.rochester.edu/~yzhu104/lean-gccjit/Lean/Meta/Match/Value.html>
- Lean Language Reference, *Pattern Matching*, "Literals" ("Natural number
  literals in patterns are interpreted by synthesizing the corresponding
  OfNat instance and reducing the resulting term to normal form, which must
  be a pattern").
  <https://lean-lang.org/doc/reference/latest/Terms/Pattern-Matching/>
- Agda API, `Agda.TypeChecking.CompiledClause` (`Case` with
  `conBranches`, `litBranches` "Map from literal to case subtree", and
  `catchAllBranch`).
  <https://hackage-origin.haskell.org/package/Agda-2.6.3/docs/Agda-TypeChecking-CompiledClause.html>
- Agda source, `Agda.TypeChecking.Patterns.Abstract.expandLitPattern`
  ("Expand literal integer pattern into suc/zero constructor patterns",
  refusing literals above 20).
  <https://hackage-origin.haskell.org/package/Agda-2.6.20240714/candidate/docs/src/Agda.TypeChecking.Patterns.Abstract.html>
- Idris 2 source, `Core.Case.CaseTree` (`ConstCase : Constant -> CaseTree
  vars -> CaseAlt vars`, "match against a literal", and `DefaultCase`).
  <https://idris2docs.sinyax.net/data/idris2/docs/Core.Case.CaseTree.html>
- Agda manual, *Built-ins* ("Closed natural numbers are represented as
  Haskell integers at compile-time").
  <https://agda.readthedocs.io/en/latest/language/built-ins.html>

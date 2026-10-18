# Proposal: number patterns without `Succ` chains

**Status:** implemented (option B), 15 October 2026; see
[As built](#as-built). Draft 1 was reviewed externally; the review
recommended option B with corrections, which draft 2 adopted (see
[Changes since draft 1](#changes-since-draft-1)).

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
  `k + x`, is kept as "`k` `Succ`s around `x`" (a *successor prefix* of
  length `k`). A few prelude functions run natively on numbers (`add`,
  `eqNat`, `decEqNat : (m n : Nat) -> Decidable (m = n)`, …), and are
  trusted ([native numbers](native-numbers.md)).
- **Data types have no indices** (only parameters). A "vector of length `n`"
  is a function computing a type from `n`, so dependent types over numbers
  come from computation: `ResultType : Nat -> Type` defined by matching.
- **Definitions are case trees.** Equations compile (by the usual
  pattern-matrix method) to nested `case` nodes, each on one variable, with
  one branch per constructor. The kernel allows `case` *only* at the top of a
  definition's body and at the top of each branch, never inside an
  expression. In each branch, the kernel substitutes the constructor value
  for the matched variable throughout the context and the goal (that's how a
  branch learns `n = Succ m`).
- **Unfolding.** A definition applied to all its arguments unfolds only if
  its case tree can take a step all the way to a leaf; otherwise it stays
  folded (`length xs` with unknown `xs` stays `length xs`). This keeps
  conversion terminating.
- **Totality.** Exhaustiveness is checked by the elaborator and re-checked
  by the kernel (one branch per constructor). Termination is structural: a
  recursive call must pass, in some fixed position, a variable bound by a
  `case` on that parameter (or something matched out of it).
- **Content hashes.** Each declaration has a hash of its checked core term,
  used to reuse cached test results; there's no serialised form of core
  terms.
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
  context and goal, and the context grows by one variable per level, so for a
  single pattern the cost grows roughly with the cube of its value `N`.
  Measured with the release build of the command-line checker on an
  Apple-silicon Mac, for `f N = True; f _ = False`:

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
  literals like a constructor column whose list of constructors is never
  complete: one branch per literal that appears, plus a default.
- **Lean 4.** A `Nat` literal pattern is turned into a *value* pattern, and
  the match compiler handles value patterns with `caseValues`, which splits a
  goal `C x` into one subgoal per listed value plus a catch-all, requires
  decidable equality on the type, gives each value's subgoal a hypothesis
  `x = v` and substitutes it, and can give the catch-all the inequalities.
  This happens in the elaborator, with Lean's general `subst`/`casesOn`
  machinery; the kernel never sees a literal pattern.
- **Agda.** Its internal case trees (`CompiledClauses`) have a `Case` node
  with constructor branches, a map from *literal* to subtree
  (`litBranches`), and a catch-all branch. Separately, the type checker has
  `expandLitPattern`, which rewrites a natural-number literal pattern into
  `suc`/`zero` patterns and refuses literals above 20. We didn't establish
  exactly when each path is taken.
- **Idris 2.** Case trees branch only on variables, with alternatives for
  constructors, `ConstCase` for a literal of a primitive type, and a
  `DefaultCase`. We haven't confirmed how a `Nat` literal *pattern* is
  checked.
- **Rocq.** `nat` numerals in patterns are, as far as we know (not re-checked
  for this note), notation for `S (S … O)`: a chain, like Stitchwort today.

Agda's `litBranches` and Idris's `ConstCase` are **precedents for the
representation** (a literal switch with a default in the case-tree
language). They are not evidence for the *typing rule* proposed below: we
haven't established that either system checks `Nat` literal branches this
way, so the soundness argument stands on its own.

## Options

### A. Elaborate to existing terms (Lean's approach)

Compile a number test to `elimDec (decEqNat n 404) (\h -> yes) (\h -> no)`,
where `elimDec : Decidable p -> (p -> a) -> (Not p -> a) -> a`. The kernel
already checks all of this, and `decEqNat` runs natively, so a test is one
step.

No new kernel feature, but a poor fit for this kernel:

- **`case` may only appear at the top of a definition.** A test written as a
  function application isn't at the top. Without generated helper
  definitions or other restructuring, this encoding can't preserve the
  existing nesting of case-tree splits: constructor splits would have to
  come before number tests. Helper definitions (one per subtree below a
  test, each with its case tree at the top) could avoid that, but they'd
  have to lift the right dependent context and preserve termination
  checking (the recursive calls would move into the helpers) and the
  unfolding behaviour.
- **The matched branch has to learn `n = 404` from `h`.** For a goal that
  mentions `n`, the branch's value must be transported along `h` with `J`,
  and so must every argument whose type mentions `n` ("generalise, then
  rewrite"), written by hand in the elaborator.
- **Definitions would unfold differently.** A test inside an application
  isn't a case-tree step, so `statusText n` with unknown `n` would unfold to
  a chain of stuck `elimDec`s, where today it stays `statusText n`.
- **The JavaScript would build** a `Decidable` object and two branch
  closures per test, unless the JS backend learned to recognise the shape.

This is an engineering trade-off, not an impossibility; B is preferred.

### B. A number switch in the case tree — recommended

Add one node to the kernel's case trees:

```
NumCase(n, [(k₁, b₁), …, (kₘ, bₘ)], d)
```

"If variable `n` is `k₁`, take `b₁`; …; if it's `kₘ`, take `bₘ`; otherwise
take the default `d`." Its parts are specified below: kernel invariants and
checking, evaluation, the pattern compiler, extraction.

### C. Keep `Succ` chains but make them cheaper

Share work between levels, or skip re-substituting variables that can't
mention the scrutinee. This could lower the constant and maybe the exponent,
but a pattern `10^30` still can't be a chain: the tree is proportional to
the value. Rejected.

## B in detail

### Kernel invariants

The kernel checks these itself; they aren't promises from the elaborator. A
violation is `E-MALFORMED` (a compiler bug, not a user error).

1. `n` is a variable in scope whose type is the registered `Nat` type.
2. The keys `k₁ < k₂ < … < kₘ` are natural numbers in strictly increasing
   order (so there are no duplicates).
3. **`m ≥ 1`.** An empty table is non-canonical and rejected; the elaborator
   never produces one (a column with no numbers isn't compiled to a
   `NumCase`).
4. The default `d` is present (it's a required field of the node, so this is
   enforced by the term's type; there's no deserialisation boundary to test,
   since core terms aren't serialised).
5. A `NumCase` appears only where a `case` may: at the top of a definition's
   body or at the top of a branch of a `case` or `NumCase`. Its branches and
   default are themselves case-tree positions.

### Checking

`NumCase(n, [(k₁, b₁), …, (kₘ, bₘ)], d) ⇐ G` in context `Γ`:

- each `bᵢ` is checked against `G[n := kᵢ]` in `Γ[n := kᵢ]`: the number
  `kᵢ` is substituted for `n` in every variable's type and value and in the
  goal, exactly as a `case` branch substitutes `Succ m`;
- `d` is checked against `G` in `Γ`, unchanged.

### Why it's sound: one-way conservativity

The claim is:

> Every well-typed `NumCase` has a well-typed expansion into ordinary
> constructor `case`s, with corresponding evaluation behaviour. The converse
> need not hold.

So a `NumCase` adds no power beyond what the kernel already accepts, assuming
the existing rules are sound. Some programs that the expansion would accept
are rejected (see "the default-branch regression"); that is the price of the
simpler rule.

**The expansion.** Let `K = kₘ` (the largest key). Expand by peeling one
`Succ` at a time, `K + 1` levels deep:

```
expand(n, j, table, d) =                       -- n is known to be j + p,
  case p of                                    -- where p is the current variable
    Zero    -> if j is a key kᵢ then bᵢ[σ] else d[σ]
    Succ p' -> if j = K then d[σ'] else expand(n, j + 1, table, d)  -- on p'
```

starting with `p = n`, `j = 0`. At each leaf, `σ` is the substitution the
constructor path has introduced: the original variable `n` is replaced by
the value it is known to have on that path, `Succ (Succ … (Succ Zero))` (`j`
`Succ`s, i.e. the number `j`) on a `Zero` leaf, or
`Succ (Succ … (Succ p'))` (`K + 1` `Succ`s around the last predecessor) on
the final `Succ` leaf; and every variable index in the copied branch is
shifted past the predecessors bound on the way. The copies are properly
scoped, specialised copies: `n` in a copy of `d` must still mean the
original value, not the current predecessor; dependent types of local
variables, the result type and the body all refer to the corresponding
values.

**Typing.** On a `Zero` leaf at depth `j = kᵢ`, the `case` rule has
substituted the number `kᵢ` for `n` in context and goal, exactly what the
`NumCase` rule did for `bᵢ`, so `bᵢ[σ]` checks. Every other leaf holds
`d[σ]`; `d` was checked in `Γ` against `G` for arbitrary `n`, and the
standard typed-substitution property (a term checked for a variable stays
checked after substituting a well-typed value for it, here the value the
path has fixed) makes `d[σ]` check against `G[σ]` in `Γ[σ]`, which is what
the `case` rule asks for at that leaf. "More information can't hurt" is the
intuition; correct substitution is the mechanism.

**Evaluation.** On a number `v`: the expansion reaches the `Zero` leaf at
depth `v` if `v ≤ K` (taking `bᵢ` if `v = kᵢ`, else `d`), or the final
`Succ` leaf if `v > K` (taking `d`); `NumCase` takes the same branch. On a
successor prefix `k + x` with `x` unknown: the expansion peels `k` `Succ`s
without looking at `x`; if `k > K` it reaches the final `Succ` leaf (taking
`d`) without inspecting `x`, and otherwise it must inspect `x` and is stuck.
`NumCase` does exactly this (see the rule below). On anything else, both are
stuck.

### Evaluation

Selecting a branch for scrutinee value `v` (after forcing solved
metavariables, as for `case`):

- `v` is a number: binary-search the keys; take the matching branch or `d`.
- `v` is a successor prefix `k + x` (including a chain of `Succ`
  constructors around an unknown, and nested prefixes, all normalised by the
  existing view of numbers): if `kₘ < k`, take `d`; otherwise stuck. The
  boundary is strict: `kₘ = k` is stuck, since `x = 0` would match.
- anything else (a variable, a stuck call, an unsolved metavariable): stuck.

**Failure to establish that `v` equals a key is never evidence that `v`
differs from it.** The implementation must not compare `v` with each key by
conversion and take `d` when every comparison fails: for an open `v` that
would be wrong. It distinguishes exactly three cases: a concrete number, a
certified successor prefix, and anything else (blocked).

**Substitution stability.** Once a successor prefix justifies taking `d`,
every later well-typed substitution for its unknown tail still does: the
value is at least `k > kₘ` whatever the tail becomes. The strict lower-bound
rule has this property. Conversely, a *blocked* value can become a listed
one after a metavariable is solved (`403 + ?m` with `?m := 1`); a blocked
result must not be cached as a decision. This is the existing behaviour for
`case` (a stuck definition stays a folded call, which is evaluated again
when it's next forced or re-evaluated after solving); `NumCase` reuses it
and is tested on exactly this example.

**A blocked subtree.** Selecting a branch doesn't mean the definition can
return: the selected subtree may be blocked on another variable (a number
test followed by a `case` on a `Bool`). Then the definition stays folded,
with its original arguments, through the existing mechanism (the evaluator
tracks the definition and its arguments while walking the case tree, and
returns the folded call if any node is stuck). No new partially unfolded
form is introduced.

Required behaviours, for

```
def hit : Nat -> Bool
  | 404 => True
  | _   => False
```

| scrutinee | required |
|---|---|
| `404` | `True` |
| `403`, `405` | `False` |
| an unknown `x` | stuck: `hit x` stays folded |
| `404 + x` | stuck (`x = 0` would match) |
| `405 + x` | `False` |
| `403 + x` | stuck (`x = 1` would match) |
| `403 + ?m`, then `?m := 1` | stuck, then `True` |

and, as a kernel test, `bad : (x : Nat) -> hit x = False` with
`bad x = rfl` must be rejected.

### Termination

- A `NumCase` introduces no new evidence of structural descent: it binds no
  variables, and a number key is never "smaller than" anything.
- Evidence from surrounding constructor `case`s is kept: a variable matched
  out of a parameter before the `NumCase` is still smaller inside every
  branch and the default.
- Every child, each listed branch **and the default**, is traversed by the
  termination checker. (Binding nothing isn't enough if an implementation
  skipped a subtree.)

So `f (Succ n) = … f n …` is accepted exactly where it is today (that
recursion goes through a `case`), and the must-reject examples (rebuilding
the matched value, `loop (Succ n) = loop (Succ n)`) stay rejected.

### The pattern compiler

The elaborator compiles equations by the usual matrix method; this changes
only how a column is split.

1. **The first-row base case comes first.** If the first remaining row
   matches whatever is left (only variables and `_`), it's the result, as
   today, before any column is classified. So in
   `constant n = 1; constant 404 = 2` the second equation is unreachable
   and `constant` doesn't inspect `n`.
2. **Choosing the column** is unchanged: the first column where the first
   row has a refutable pattern (a constructor or a number).
3. **Classifying it.** If any row has an explicit `Zero` or `Succ` pattern
   in that column, it's split with a constructor `case`, as today: in the
   `Succ` branch a number `k > 0` becomes `k - 1` on the predecessor, and
   `0` belongs to the `Zero` branch. Otherwise (numbers, variables, `_`) it
   becomes a `NumCase`. Constructor splits happen only where the source
   writes explicit `Zero`/`Succ` patterns, so how deep the tree gets depends
   on the explicit pattern structure, not on the values of the literals.
   (Keep this rule for now; splitting on constructors only where the first
   row has one could change which open terms reduce.)
4. **The keys** are the distinct numbers in the column, sorted. Repeated
   source literals merge into one key: `g 404 True = 1; g 404 False = 2;
   g _ _ = 3` gives one `404` entry whose subtree splits on the `Bool`. The
   kernel's unique-key rule is about the core term, not the source.
5. **A listed branch keeps every applicable row**, in order: the rows with
   that number there, and the rows with a variable or `_`. The default keeps
   the rows with a variable or `_`. Failing a later column inside the `404`
   branch falls through to the next applicable row in that branch, not to
   the switch's default. With

   ```
   g : Nat -> Bool -> Nat
   g 404 True  = 1
   g n   False = n
   g _   _     = 3
   ```

   `g 404 True = 1`, `g 404 False = 404`, `g 405 False = 405`,
   `g 405 True = 3`. The row `g n False = n` runs with `n = 404` in the
   `404` branch; it doesn't acquire an assumption `n ≠ 404`.
6. **Variables bind the original value.** A variable pattern names the
   value of the column it appears in, even after constructor splits on that
   column have introduced predecessors. Regression test:

   ```
   h 404              = 0
   h (Succ (Succ k))  = k
   h n                = n
   ```

   `h 1` must be `1` (not the predecessor `0`), `h 0 = 0`, `h 404 = 0`,
   `h 405 = 403`.
7. **Exhaustiveness.** A `NumCase` needs a default, so a column of only
   numbers with no variable or `_` row is `E-NONEXHAUSTIVE`, naming the
   numbers that are handled.
8. **The cap is removed.**

### The default-branch regression, and the policy

The default is checked knowing nothing about `n`, where the old expansion
knew more on each path. This affects ordinary dependent programs, not just
proofs:

```
def ResultType : Nat -> Type
  | Zero   => Nat
  | Succ _ => Bool

def make : (n : Nat) -> ResultType n
  | 0 => 0
  | n => False
```

Today the second equation is checked knowing `n = Succ m`, so
`ResultType n` computes to `Bool` and `False` checks. With `NumCase`, it's
checked for an arbitrary `n`: `ResultType n` doesn't compute, and `False` is
rejected. The repair is to say what's meant:

```
def make : (n : Nat) -> ResultType n
  | Zero   => 0
  | Succ _ => False
```

The policy, uniformly, with no special threshold for small numbers:

> A number pattern tests for a value. Explicit `Zero`/`Succ` patterns expose
> structure. A catch-all after number patterns learns nothing about the
> value: no predecessor, and no exclusions.

So `0` and `Zero` in a pattern can lead to different checking. Inequalities
in the default (`Not (n = 404)`, as Lean can provide) would be useful for
some programs (excluding zero for a division), but they're a separate
feature and don't restore constructor refinement (`ResultType n` still
wouldn't compute), so not in this milestone. Where evidence is needed, match
on constructors or use `if h : n = 404 then … else …`.

**A targeted diagnostic.** When checking a `NumCase` default fails, and the
goal or a variable's type mentions the scrutinee, the error gets a note:
"number patterns test values: in this equation, nothing is known about `n`.
To use its shape, match on `Zero` and `Succ` instead of `0`." (Wording to be
settled with the snapshot tests.)

Nothing in the repository's examples or prelude is affected, as far as a
read of them shows: the prelude's `isSpaceCode` and `digitChar` use only
numbers and `_` with non-dependent results, and `half`, `fib` and `peel`
mix in `Succ` patterns, so they keep the `case` split. The implementation's
test run will confirm it.

### Other consumers of case trees

Every place that understands `case` must understand `NumCase`. The audit
list (from reading the code; each gets a test or a line of review):

- **Kernel checking** (the rule above), and the "case only in a case tree"
  position check.
- **Termination checker** (above: traverse every child, keep outer
  evidence).
- **Scope and substitution:** shifting variable indices, "does this term
  mention variable `i`" (the scrutinee counts as a mention), the
  elaborator's metavariable substitution (zonking), freeing deep terms
  without recursion.
- **Both evaluators** (the main abstract machine and the independent
  reference evaluator), and the unfolding policy.
- **Content hashing:** the scrutinee, every key, every branch and the
  default contribute to the declaration's hash, and so does a reference to
  the `Nat` type (as a `case` hashes its data type). Changing `404` to
  `405` must change the hash, invalidating cached test results. Canonical
  key order helps but doesn't replace hashing all the content.
- **Pretty-printing** of core terms (in error messages).
- **Dependency collection:** what a definition refers to (for extraction's
  reachability and for hashing).
- **JS extraction:** a `switch` on the `bigint`, each listed branch as a
  `case 404n:` block, then the default. This avoids the `Decidable` object
  and branch closures option A would build; the exact runtime strategy
  (`switch`, `if` chain) isn't part of the language's guarantee.
- **Serialisation:** none exists for core terms today.

### Performance: what's claimed

Numeric dispatch no longer needs work proportional to the *value* of a
literal. For a fixed context, checking does one refinement per distinct key
(`m` refinements), each costing about as much as one `case` branch today,
plus the cost of the branch bodies. That is not free: comparing and
substituting big numbers costs time in their bit length, a dependent result
type may itself compute on the literal (a value of a type with `10^30`
elements is still expensive), and rows with variables are copied into every
listed branch, so a wide table with many wildcard-heavy columns can still
grow.

To be measured separately, each with elaborator time, kernel time, peak
memory and generated JS size:

- **literal magnitude:** one key at increasing bit lengths (`2^8` … `2^100`);
- **table width:** `m` distinct keys, `m` = 10, 100, 1,000;
- **context and pattern complexity:** dependent arguments, several columns,
  wildcard-heavy tables.

The repository's benchmark suite (`crates/bench`) gets these cases.

### Testing plan

1. **A bounded constructor-expansion oracle.** A test-only function expands
   a `NumCase` with small keys into ordinary constructor `case`s (the
   expansion above, built from real `case` nodes, never calling the new
   dispatcher). For generated and hand-written definitions: if the kernel
   accepts the `NumCase` version, it must accept the expansion; and both
   must evaluate alike on numbers, successor prefixes and unknowns (the same
   result, or both stuck). The old elaborator path (number patterns as
   `Succ` chains) is kept as a test-only option, bounded to small numbers,
   so whole programs can be compared too.
2. **Compiled patterns against a source-row matcher.** A tiny matcher that
   tries the source equations top to bottom on closed inputs gives the
   expected result; the compiled case tree must agree (first-match priority,
   rows kept in listed branches, variable bindings: the `g` and `h` examples
   above, plus generated tables).
3. **Reference evaluator against generated JS**, under Node, especially
   mixed constructor/number columns and large numbers (`10^30`).
4. **Kernel tests on hand-built terms that must be rejected:**
   - a listed branch whose body is only valid for a different key, and a
     default that tries `rfl : n = 404`;
   - refinement of dependent arguments in one branch, with a sibling branch
     that would only type-check if the refinement leaked into it;
   - non-decreasing recursion hidden in a listed branch, and in the default;
   - a malformed scrutinee (not a variable in scope, not of type `Nat`),
     duplicate keys, unsorted keys, an empty table;
   - a `NumCase` inside an expression rather than a case-tree position;
   - `bad x = rfl` for `hit x = False` (above).
   And one that must be accepted: a recursive call on a structural
   descendant established by a `case` *before* the `NumCase`, so the new
   node doesn't discard existing evidence.
5. **Evaluation tests:** the `hit` table above, including the metavariable
   example, nested successor prefixes, solved metavariables inside a
   prefix's tail, and the zero-offset case (`0 + x`, which is just `x`).
6. **End to end:** `statusText` with codes 200…503 and a fallback (checking
   time, results in the CLI, the evaluator and JS), a dependent result where
   a branch needs `n = k`, the `ResultType`/`make` regression and its
   diagnostic, several columns, `E-NONEXHAUSTIVE`, termination cases, and
   the existing differential tests.

## Text and characters

There are no `Char` or `Text` literal patterns today. A `Char` pattern `'a'`
could later be sugar for `MkChar 97 _` (a `Char` is its code plus a proof
that the code is valid), which this design already compiles well: a `case`
on `MkChar`, then a `NumCase` on the code. A `Text` pattern would be a
`case` on the text's list of characters, one character at a time, so linear
in its length. Neither is part of this change.

## Open questions

1. **The diagnostic's trigger.** "The default failed and the goal or
   context mentions the scrutinee" may fire on errors unrelated to the
   number pattern. Is a note that's occasionally irrelevant acceptable, or
   should it require that the failure involve a stuck computation on the
   scrutinee?
2. **Default inequalities later.** If they're added, how should the surface
   syntax name the proof, given that a wildcard equation isn't necessarily
   (only) the default (it also runs inside listed branches, where the
   inequality would be false)?

## Changes since draft 1

Adopted from the external review:

1. The soundness claim is now **one-way conservativity** (every well-typed
   `NumCase` has a well-typed expansion into ordinary `case`s with
   corresponding evaluation; not the converse), with the expansion's
   substitutions spelled out. Draft 1's "conversion gives the same answers,
   and so does type checking" overstated it.
2. **Termination:** no new descent evidence, surrounding evidence kept,
   every child including the default traversed.
3. **Kernel-checked invariants:** scrutinee a `Nat` variable, keys strictly
   increasing, default present, case-tree positions only; an **empty table
   is rejected** as non-canonical.
4. **The default-branch regression** is documented with the
   `ResultType`/`make` example (an ordinary dependent program, not just a
   proof), with the uniform policy (numbers test values, `Zero`/`Succ`
   expose structure, no threshold, no default inequalities this milestone)
   and a targeted diagnostic.
5. **Evaluation:** the `k + x` rule with `kₘ < k` (strict), the `hit` table,
   "failure to establish equality is never disequality", substitution
   stability, metavariable re-forcing (`403 + ?m`), and blocked selected
   subtrees reusing the existing folding mechanism.
6. **Pattern compiler details:** listed branches keep applicable wildcard
   rows (the `g` example), repeated source literals merge into one key, the
   first-row base case stays first, the mixed-binding test `h`, and "only as
   many levels as the source writes `Succ`s" softened (explicit `Zero` also
   forces a split; depth depends on pattern structure, not literal values).
7. **Testing plan:** a bounded constructor-expansion oracle using real
   `case`s, the old small-number compiler kept as a test-only path, a
   source-row matcher on closed inputs, reference against JS, and the
   invalid-kernel tests including `bad x = rfl`.
8. **Performance claims** tightened: named variables (value of the literal,
   number of distinct keys), separate measurements of magnitude, table width
   and context complexity, and the JS benefit worded as avoiding the
   `Decidable` object and closures.
9. **Audit of every case-tree consumer**, including keys and default in the
   declaration hash.
10. **Option A** softened to an engineering trade-off (helper definitions
    could restructure it), and the prior art qualified as precedent for the
    representation, not for the typing rule.

Draft 1's five open questions were answered by the review (B; no default
inequalities yet; no small-number threshold; keep the "any constructor in
the column" rule; the `k + x` default with a strict bound) and are folded in
above.

Not adopted, or adapted:

- **Deserialisation-boundary tests** for invariants enforced by the term's
  type: there's no serialised form of core terms, so there's nothing to
  test; the note records that instead.
- **Metavariable re-forcing:** the review asks that forcing reconsider a
  blocked match after a solution. In this codebase, a stuck definition call
  stays a folded call and is evaluated again when re-evaluated after
  solving, rather than being "re-forced" in place; `NumCase` reuses that
  unchanged, and the `403 + ?m` test checks the observable behaviour.
  Exactly where re-evaluation happens during unification hasn't been traced
  for this note.

## As built

Option B as specified above, with these specifics.

- **The node** is `Term::NumCase(x, arms, default)` in `crates/core/src/term.rs`
  (`NumArm` holds a number and a body). The kernel rule is
  `check_num_case` in `crates/core/src/check.rs`. Every invariant in
  [Kernel invariants](#kernel-invariants) is checked there or by the
  existing position check (`case_only_in_tree`), and a violation, including
  a scrutinee that isn't a `Nat`, is `E-MALFORMED`. For admission, a
  number case counts as a use of `Nat` (`admissible`), and like `case` it's
  refused while the type it matches on isn't finished.
- **Evaluation.** The machine (`value.rs`, `branch`) uses the existing view of
  numbers (`native::view`, which forces solved metavariables along the way)
  and distinguishes a number (binary search of the keys), `k + x` (the
  default only if the largest key is below `k`) and anything else (stuck,
  so the definition stays folded). The reference evaluator does the same
  with a linear search, sharing only the view. Metavariables: a scrutinee
  that needs forcing is forced first, exactly as for `case`; a stuck call
  is re-evaluated when next forced, which is what the `403 + ?m` test sees.
- **The pattern compiler** (`compile_numbers` in `crates/elab/src/lib.rs`)
  follows rules 1 to 8 above. Rows are grouped by number once, so a table
  of `m` numbers is compiled in time about linear in `m` (a first version
  filtered every row for every number, which was quadratic: 4.7 ms for
  1,000 rows instead of 1.2 ms). The elaborator checks the tree with the
  same refinement as the kernel before the kernel re-checks it.
- **The diagnostic** is added when checking the default fails with
  `E-TYPE-MISMATCH`, `E-NOT-EMPTY` or `E-REFL` and the goal, or the type of
  a variable bound after the scrutinee, mentions it (open question 1: the
  broader trigger, accepting an occasionally irrelevant note). Its wording:
  "number patterns only test values: an equation with a variable or `_`
  where the others have numbers knows nothing about `n`, not even that it's
  a different number. To use the shape of `n`, match on `Zero` and `Succ`
  instead".
- **The old compilation** stays as `Elaborator::numbers_as_succ`, a flag
  only tests set. It's a public field rather than `#[cfg(test)]` because the
  tests that use it are integration tests in another crate.
- **Other consumers:** termination (walks every arm and the default, adds
  nothing), shifting and `mentions` (the scrutinee counts), zonking,
  freeing without recursion, hashing (tag, scrutinee, `Nat`, the number of
  arms, each number and arm, the default), pretty-printing (`case x of …`,
  as for `case`), and JS (a `switch` on the `bigint` with a `case 404n:`
  block per arm, each of which returns or continues a loop, then the
  default). Dependency collection needed nothing: the node refers to no
  definition, and its children are visited by the generic traversal.

Behaviour changes that users can see: the 256 cap and its `E-UNSUPPORTED`
error are gone; `make 0 = 0; make n = False` style programs (a catch-all
that needs `n` to be a `Succ`) are now rejected with the note above, where
they were accepted before (none in the repository's examples or prelude
were); and on *open* arguments, definitions can unfold differently from the
old `Succ` chains, in both directions. On closed arguments the two
compilations agree (the generated tests check it). For example, a
generated definition applied to `6 + x`:

```
def f : Nat -> Nat
  | 4 => 100
  | _ => 101
  | Succ (Succ y) => y
  | 6 => 103
  | Succ 1 => 104
  | Zero => 105
```

The old chain for `4` peeled `Succ`s, found it isn't `4`, and fell through
to `f _ = 101`. Now, after the two constructor splits that the `Succ`
patterns force, a number case on the remaining `4 + x` has keys `0`, `2`
and `4` (from `Succ 1`, `4` and the unreachable `6`), so it's stuck: `x`
could be `0`. Conversely, a number case rules out all of a column's
numbers at once on `k + x`, where the old chain, having ruled out the first
row's number, could go on to split another column on an unknown and get
stuck. Neither changes what a closed program
computes; both follow from the specified rule (unreachable rows still
contribute keys).

### Tests

In `crates/driver/tests/number_patterns.rs`:

- the kernel rejects a listed arm valid only for another number, `rfl : n =
  404` in the default and in an arm for another number, a sibling arm that
  would need a leaked refinement, a default that relies on refinement,
  hidden non-decreasing recursion in an arm and in the default; it accepts
  recursion on a predecessor matched by a `case` before the number case;
  and it rejects an empty table, a repeated key, unsorted keys, a
  scrutinee out of scope or not a `Nat`, and a number case inside an
  expression;
- the `hit` table, in both evaluators, including `0 + x`, `Succ (404 + x)`,
  `403 + ?m` before and after solving `?m := 1`, and a solved metavariable
  applied to an argument inside a prefix;
- hashes differ when a key or the default changes, and agree for equal
  bodies;
- the oracle: 300 generated definitions (one to three columns of `Nat` or
  `Bool`; numbers up to 6, `Zero`, `Succ` patterns, variables, `_`) are
  compiled with number cases and checked against a matcher that tries the
  source rows in order, against the old `Succ`-chain compilation, and
  against the expansion of each number case into ordinary `Zero`/`Succ`
  `case`s, which the kernel must accept; on open arguments (`x`, `1 + x`,
  `6 + x`, `7 + x`) the compiled definition and its expansion must both be
  stuck or both give the same result. The examples' and prelude's number
  cases with small keys are expanded and checked too.

In `examples/`: `accept/number-patterns.sw` (`statusText`, `10^30`, a
dependent result and dependent argument, `g`, the repeated-literal `g2`,
`h`, `constant`, recursion through `Succ` with a number column, the
`make` repair), `extract/number-patterns.sw` (the same against the
reference evaluator in Node, plus random inputs), `reject/number-pattern-default.sw`
(the `make` regression and its note), `reject/number-patterns-missing-case.sw`,
and in `soundness/` `bad x = rfl`, a default claiming `n = 404`, and
`loop n = loop n` after a number pattern.

### Performance

Release build of the command-line checker, Apple-silicon Mac, median of
three runs; elaborator and kernel time for the one definition (measured
with temporary instrumentation around the elaborator's `body` and the
kernel's `define_def`), wall time and peak resident memory of the whole
process; generated JS includes about 10 kB of runtime.

| program | before: elab / kernel / wall / peak | after: elab / kernel / wall / peak |
|---|---|---|
| `f 100` | 64 ms / 64 ms / 0.15 s / 21 MB | < 0.01 ms / < 0.01 ms / 0.01 s / 6 MB |
| `f 256` | 989 ms / 993 ms / 2.0 s / 231 MB | < 0.01 ms / < 0.01 ms / 0.01 s / 6 MB |
| `f 2^16`, `f 10^30`, `f 2^1000` | `E-UNSUPPORTED` | ≤ 0.01 ms / < 0.01 ms / 0.01 s / 6 MB |
| table of 100 | 63 ms / 62 ms / 0.15 s / 22 MB | 0.13 ms / 0.08 ms / 0.02 s / 6 MB |
| table of 256 | 1009 ms / 988 ms / 2.0 s / 234 MB | 0.33 ms / 0.21 ms / 0.02 s / 7 MB |
| table of 1,000 | `E-UNSUPPORTED` | 1.2 ms / 0.7 ms / 0.02 s / 8 MB |
| table of 10,000 | `E-UNSUPPORTED` | 12 ms / 7 ms / 0.04 s / 23 MB |
| 50 keys, three arguments of type `Shape n` | 65 ms / 64 ms / 0.15 s / 22 MB | 0.24 ms / 0.20 ms / 0.02 s / 6 MB |
| 3 number columns × 5 keys, `_` elsewhere | 42.6 s / 42.8 s / 85 s / 157 MB | 0.04 ms / 0.03 ms / 0.01 s / 6 MB |
| 3 number columns × 20 keys | stopped after 5 minutes, over 2.6 GB | 0.18 ms / 0.11 ms / 0.01 s / 6 MB |

Generated JS: `f 200` 230 kB before, 10 kB after; the table of 256 357 kB
before, 21 kB after; 3 columns × 5 keys 76 MB before, 11 kB after.

The benchmark suite has `check-number-huge`, `check-number-wide`,
`check-number-dependent` and `check-number-columns` for these, alongside
`check-number-pattern` and `check-number-table` (which went from about
1 s and 2 s to under 1 ms each). Prelude functions with number patterns
(`digitChar`) also evaluate in one step now, which shows in
`text-nat-to-text` and `run-prints` (about 12% fewer allocations).

### Not done

- The review's "deserialisation boundary" tests: there's no serialised form
  of core terms (as noted above).
- Default inequalities and `Char`/`Text` patterns, as planned.

## Sources

- L. Maranget, *Compiling Pattern Matching to Good Decision Trees*, ML
  Workshop 2008, pp. 35–46 (constants are handled as constructors of a type
  whose signature is never complete, so a default matrix is always needed).
  <https://doi.org/10.1145/1411304.1411311>
- J. Cockx and A. Abel, *Elaborating Dependent (Co)pattern Matching*,
  ICFP 2018 (case trees for a dependently typed core, as in Agda).
  <https://doi.org/10.1145/3236770>
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

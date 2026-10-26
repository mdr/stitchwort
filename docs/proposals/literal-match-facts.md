# What a literal match's catch-all arm knows

**Status:** built on a branch, 26 October 2026 (SW-533, D1306). **Changes
the kernel**, so it waits for Matt's review before merging. User
documentation: [syntax.md, Declarations](../syntax.md#declarations) (the
paragraph on number patterns).

## The problem

A character pattern `'k'` is the number pattern `MkChar 107 _`, and number
patterns compile to a number case, `NumCase(x, [(k₁, b₁), …], d)`
([number-patterns.md](number-patterns.md)). Until now the kernel checked
the default `d` knowing nothing new about `x`, and evaluation left a
number case on an unknown `x` stuck. So for

```
def commandOfChar (char: Char): Option Command :=
  match char with
    | 'k' => Some (Move North)
    …
    | _ => None
```

nothing could prove "no other key is a command": in any proof, the
program's `commandOfChar (MkChar code valid)` stays stuck for an unknown
`code`, even with `code ≠ 107`, … as hypotheses. The roguelike changed its
program to look keys up in a table instead (`games/rogue/PROOFS.md`,
"Tried"). The same gap made AoC day 4 write `parseChar` as an `if`
(docs/aoc-2025.md, day 4).

## What a proof could do before

- **(a) Reach a literal arm given `c = lit`: yes.** Transport along the
  equation: `J (y e => next y = 'b') rfl (Eq.sym h)`, or `rewrite`; once the
  character is the literal, the program's match steps
  (`examples/accept/char-pattern-proofs.sw`, `nextOfA`).
- **(b) Reach the catch-all given `c ≠ lit₁ ∧ … ∧ c ≠ litₙ`: no.** A number
  case steps only on a number, or on `k + x` with every arm's number below
  `k`. Hypotheses don't change what a term computes to, and no rewrite
  turns an unknown `c` into either form. The only way was a `Zero`/`Succ`
  split down past the largest literal, one case per number below it: 120
  levels for `'w'`, a million for `'→'`, and the cost grows like the cube
  of the depth (number-patterns.md's measurements).
- **(c) Split a literal match in a proof and get the facts in each arm: no.**
  A proof's own `match c with | 'k' => … | _ => …` got `c = 'k'` in the
  first arm (by substitution) and nothing in the second.
- `decide` and `omega` don't help: the goal isn't a closed decidable
  proposition, and `omega` doesn't look inside `commandOfChar`.

## How others do it

- **Lean 4.** The match compiler handles literal (value) patterns with
  `caseValues`
  ([source](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Match/CaseValues.lean)):
  its doc comment says it splits a goal `C x` into one subgoal per value,
  `(h_i : x = value[i]) ⊢ C value[i]`, plus a last one,
  `(h_1 : x ≠ value[0]) … (h_n : x ≠ value[n-1]) ⊢ C x` (the hypotheses
  can be left out). Each split is a `dite (x = v)` over a decidable
  equality, so the test is an ordinary term (`decEq x v`) that a proof can
  generalise and case on. The kernel never sees a literal pattern; the
  price is that a literal match is a chain of `if`s in the term.
- **Agda.** Its case trees have a map from literal to subtree beside a
  catch-all (`litBranches`, `catchallBranch`,
  [source](https://github.com/agda/agda/blob/master/src/full/Agda/TypeChecking/CompiledClause.hs)),
  the same representation as our `NumCase`. We didn't find, and didn't
  verify, what Agda's catch-all knows in a proof; we don't cite it as
  precedent for the rule below.

## Options

**A. Elaborate literal matches to a decidable-equality chain (Lean).**
No kernel change. But number-patterns.md already weighed this as its
option A and chose `NumCase` instead: a test inside an application isn't at
the top of a case tree, so constructor splits after it need helper
definitions; each arm must transport its goal along `h` by hand; calls
would unfold to chains of stuck `elimDec`s instead of staying folded; and
every backend would have to recognise the chain to keep a `switch`. And a
proof would still have to generalise each `decEq c v` in its goal by hand
for (b).

**B. A std lemma per case shape.** A lemma can't mention a `NumCase`: it's
not a term a statement can contain, only the shape of a definition's body.
Equation lemmas generated per definition (Lean's `f.eq_2` with `x ≠ v`
hypotheses) would have to be proved, and in this kernel the only proof is
the `Zero`/`Succ` split of (b) above. Not workable.

**C. A proof-side `match` that adds hypotheses.** Naming `h: c ≠ 'k'` in
the catch-all is easy for the elaborator to arrange, but it doesn't solve
(b): the hypotheses still don't make `commandOfChar (MkChar code valid)`
compute. Something has to.

**D. The catch-all knows what it isn't (chosen).** The kernel checks a
number case's default with the matched variable marked *apart* from the
arms' numbers, and evaluation lets a number case on a variable take its
default when each of its numbers is one the variable is apart from. So a
proof's `match char with | 'k' => … | … | _ => …` on the program's
literals (or more) reaches the program's `_` arm in its own `_` arm. That
gives (b): from `c ≠ 'k'`, … match on the same literals, rule out each
literal arm with its hypothesis, and the catch-all computes. And (c), in
the form a proof uses most: the facts act where they're needed, in
computation. They aren't named hypotheses; a proof that needs `c ≠ 'k'` as
a value still proves it as before.

D changes the kernel, which A avoided, but A was already rejected for
number patterns, and B and C don't reach (b). D is the smallest change
that does: no new term former, no change to checked terms or hashes,
nothing for the backends.

## The rule

- **Values.** A variable value carries what it's apart from:
  `Head::Var(level, Apart)`, where `Apart` names a sorted set of numbers
  kept in `Globals::apart_sets` (only added to, so a name never changes
  meaning), or `Apart::NONE`. It's a fact about the variable, not part of
  it: equality and hashing of heads ignore it, so a variable is equal to
  itself however it's marked, and read-back writes the plain variable. So
  checked terms, and their hashes, are what they were.
- **Checking** (`check_num_case`, and the elaborator's mirror in
  `check_tree`). If `x`'s value is still the variable itself, the default
  is checked with `x` substituted, throughout the context and the goal, by
  the variable apart from the arms' numbers and anything it was already
  apart from (a default nested in a default on the same variable knows
  both). Otherwise (the variable was already refined, which the elaborator
  never produces) the default is checked as before. Substitution for a
  later case keeps other variables' marks (`substitute_in`).
- **Evaluation** (`value::branch`, and the reference evaluator alike). A
  number case on `k + x`, `x` a variable apart from a set `S`, takes the
  default when every arm's number `a` is below `k` or has `a - k` in `S`.
  (`k = 0` is `x` alone.) Before, it took the default only when every `a`
  was below `k`.

### Why it's sound

A default is taken, when anything runs, only for a number none of the
arms has, or for `k + p` with every arm below `k`, or (now) for a variable
apart from every arm. In each case the scrutinee is none of the arms'
numbers, so marking `x` apart from them in the default states something
true of every value `x` can have there. And the evaluation rule only ever
sends a number case to its default when its scrutinee can't be any of its
numbers: `k + x` with `x ∉ S` is never `a` when `a < k` or `a - k ∈ S`.

The proposal's soundness argument for `NumCase` (one-way conservativity:
it accepts no more than the nested `Zero`/`Succ` cases it stands for)
still holds. Each copy of the default in the expansion has `x` either a
number other than the arms', or `kₘ + 1 + p` past every arm, and at each a
number case that the apart rule sends to its default takes the default by
the old rules too: a concrete `n ∉ S` makes `k + n` none of the arms'
numbers, and `kₘ + 1 + p` makes `k + x` bigger than every arm. The oracle
test `every_number_case_in_the_examples_has_an_expansion_that_checks`
(`crates/driver/tests/number_patterns.rs`) now also expands the new
example's proofs into `Zero`/`Succ` cases and the kernel accepts each
expansion, which uses no apart marks at all. (It skips `kindNested`, a
number case nested in another's default on the same variable: there the
expansion can't follow, since a `case` on a variable already refined to
`k + p` learns nothing about `p`; that's a limit of the oracle, not of the
rule.)

`examples/soundness/literal-match-default-unlisted.sw` is the near miss:
a proof's catch-all that leaves out one of the program's literals can't
compute the program's match, and is refused with a counterexample.

## Cost

- **Running: none.** The core term is the same `NumCase`; the machine,
  native code and JavaScript lower it as before, and a running program
  never has a variable to be apart.
- **Checking.** A default arm now substitutes into the context and the
  goal once, as each numbered arm always has: one more arm's worth of
  work per number case. A number case stuck on a variable checks for a
  mark (one load) before staying stuck. Not measured against the old
  build; the roguelike, proofs included, checks from cold in about 5 s of
  CPU.

## What it doesn't do

- **No shapes.** Apart from `0` isn't `Succ` of something: a match on
  `Zero` and `Succ` (`ResultType n`) still doesn't compute in a default
  after `| 0 =>` (`examples/reject/number-pattern-default.sw`).
- **Arithmetic other than `k +`** (`n + 2` as a call of `add`, `n * 2`)
  isn't looked through.
- **The facts aren't named.** Naming `h: c ≠ 'k'` in the catch-all (option
  C) could be added on top later if proofs want them as values.
- **Index unification and refinement through indexed families**
  (`families.rs`, `unify_index.rs`) rebuild values without marks, so a
  default arm that then splits an indexed family loses them: incomplete,
  not unsound.
- **`auto`** can't decide membership in a list of more than about seven
  literals (its search stops 8 deep); the roguelike decides `char ∈
  commandKeys` with `Decidable.fromYes` instead.

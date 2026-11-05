# Pattern guards, `| p if c => e`: how to build them (SW-1295)

**Status:** implementation note, 4 November 2026, for a Sonnet lane. The
language decision is D2371 (Matt, 4 Nov 2026): guards in every `match` (`match
… with`, definitions' arms, `match | …`, `match some | …`, `matches | …`);
when `c` is false the arms below are tried; a guarded arm covers nothing for
exhaustiveness; proofs see an ordinary `if`. This note settles the details
inside that. It replaces the sketch in
[partial-lambdas.md](partial-lambdas.md) §6 and revives SW-237 (pruned in
October without a note): the arm knows `c`, the arms below know `not c`, by
the rule of an `if`.

Claims about Stitchwort are **[checked]** when I read the code named (on
`main` at `f14eff602`), **[estimate]** when they are my reading of what will
happen. Line numbers are at that commit.

## 1. In short

- **Syntax.** `if c` after an arm's last pattern, before `=>`:
  `| (j, y) if j != i => (x, y)`. It covers the whole arm: every pattern of
  a several-pattern arm, and every alternative of an or-pattern (`| A | B if
  c =>` is "`A` or `B`, and `c`"). `if h: P` names the fact, as in an `if`
  expression.
- **Compiling.** In the elaborator's case-tree compiler, where a row becomes
  a leaf (it matches whatever is left), a guarded row becomes a new node
  `Tree::Guard`: the leaf, and an `else` tree compiled from the rows below
  it in the same branch. Checking it is `check_if` with the arm's body as
  `then` and the `else` tree as `else`, so the kernel term is exactly what
  `if c then … else …` gives today (`ifThenElse`, or `Decidable.elim` when the
  condition is a decided proposition).
- **Facts.** Whatever `if c then a else b` lets `a` and `b` know, the arm
  and the arms below know: `_: c` in the arm and `_: Not c` below for a
  decided proposition (`n != 0`, `x < y`), nothing for a plain `Bool`; with
  `if h: P`, `h: P` in the arm (the `Not P` below stays unnamed).
- **Coverage.** A guarded row's `else` with no rows left is a missing case,
  so `E-NONEXHAUSTIVE` falls out, with a note naming the guarded arm. The
  `W-REDUNDANT` and `W-MATCH-TOTAL` checks need two small changes.
- **Equations.** Arms before the first guarded arm keep theirs exactly.
  Stage 1 generates none from the first guarded arm on (recorded, so
  `E-NO-EQUATION` says why), and no `f.induct` for such a definition. Stage
  2, a separate Opus lane, adds them: the guard as a hypothesis of its own
  arm's equation, and as `notArmJ` for the arms it overlaps.
- **Abilities.** A guard may not perform operations (`E-ABILITY`), as `if h:`
  may not today. A pure call of an effect-polymorphic function is fine.

## 2. Syntax

### 2.1 Grammar

```
arm   ::= "|" pattern ("," pattern)* guard? ("=>" expr)?
guard ::= "if" (lower ":")? expr        -- the expression stops at a top-level `=>`
```

The `=> expr` is optional where it is today: an arm with an absurd `()`
pattern, and a `matches` arm (body `True`). An absurd arm with a guard is
`E-PARSE` ("an arm with `()` and no body can't have a condition"): the guard
would test nothing.

`if` after a pattern is a parse error today (`match_expr` expects `,` or `=>`
after the patterns, parser.rs:2504-2521; definition arms likewise,
parser/declarations.rs:665-678) **[checked]**, so no program changes meaning.

### 2.2 Where the guard's expression ends

The guard is parsed with `expr()`, with one new stop: a `=>` not inside
brackets opened since the guard started. Without it, `| x if flag => e`
would read `flag => e` as a lambda, since `lambda_ahead` (parser.rs:3491)
looks for names followed by `=>`, at the start of an expression and after
`|>` (parser.rs:3693). The precedent is `rewrite`'s rule, which ends at an
`in` or `at` outside brackets: a parser field `rewrite_rule: Option<usize>`
checked in `is_stop` (parser.rs:750-768, `ends_rewrite_rule` at 775)
**[checked]**. Add `guard_start: Option<usize>` the same way, set while the
guard is parsed and saved/cleared around it; `lambda_ahead` already refuses a
`=>` that `is_stop` says ends the expression (parser.rs:3512-3515)
**[checked]**. A lambda inside the guard is bracketed anyway
(`xs.any (x => x > 0)`) and isn't affected.

The constructor-argument stop set in `alt_pattern_one` (parser.rs:2671-2690:
`,`, `->`, `=>`, `|`, closing brackets) gets `KwIf`, so `| Some x if x > 0`
stops `Some`'s arguments at the `if` **[checked]** that the list is explicit;
whether `if` would stop it anyway is untested.

### 2.3 One-line arms, or-patterns, several patterns

- **One line.** `match n with | Zero => 0 | Succ k if k > 2 => k | _ => 1`:
  the guard ends at `=>`, the result at the next `|`, as today
  (partial-lambdas.md §5.2). `||` is a token of its own, so `| x if a || b
  =>` is one guard.
- **Or-patterns.** `alternatives` (parser.rs:2702) takes every `| q` on the
  same line before the guard, so `| 'h' | 'a' if strict => …` is one arm
  whose guard covers both, as in Rust and OCaml. An or-pattern binds no
  names (`E-OR-PATTERN-BINDS`, parser.rs:2717), so the guard means the same
  for each alternative. The compiler expands or-patterns into one row per
  alternative with the same right-hand side (`expand_or_patterns`,
  lib.rs:423) **[checked]**; each copy keeps the guard, so the guard is
  tested once for the alternative that matched (twice at most if two
  alternatives overlap, which `W-REDUNDANT` already flags). Pure guards (§7)
  make that unobservable.
- **Several patterns.** `| p, q if c =>`: one guard, after the last pattern,
  over all of them. No per-pattern guards.
- **Clause lambdas.** `match some | (j, y) if j != i => (x, y)`; `matches |
  Some x if x > 0` (no `=>`: `True`). `clause_lambda` (parser.rs:2566) parses
  arms itself, so it gets the same `guard?` call as `match_expr`. The hidden
  last arm stays unguarded.
- **`:= match | …` as a definition's body** is lowered to the arms form
  (parser/declarations.rs:316-333) **[checked]**; the lowering copies the
  guard into the equation.
- **Not in** `handle` clauses, `match induct`, `match reify`, or pattern
  `let`s and lambdas: those don't take arms of this kind, and a guard there
  stays `E-PARSE`.

### 2.4 Layout

The guard may continue on following lines indented further than the arm's
`|`, as the arm's body may: arm parsing sets `limit` to the `|` column
(parser/declarations.rs:615) and `match_expr` lines arms up by the `|`
column (parser.rs:2496-2503) **[checked]**, and nothing new is needed. The
formatter is token-based (`crates/fmt/src/layout.rs`, `spacing.rs`)
**[checked]** that it has no notion of arms; it should print `if` with a
space either side and leave the guard on the pattern's line **[estimate]**:
the lane checks `stitchwort fmt` on the new examples, and the AST
equivalence check (`crates/syntax/src/equivalence.rs`) must compare guards.

### 2.5 The tree

```rust
pub struct Guard {
    pub binder: Option<Name>,   // `if h: P`
    pub cond: Expr,
    pub span: Span,             // from `if` to the end of `cond`
}
```

A field `guard: Option<Guard>` on `ast::Alt` (ast.rs:336) and on
`Decl::Equation` (ast.rs:956). There are 18 `Alt {` and 77 `Decl::Equation
{` occurrences in the crates **[checked]**, most of them patterns with `..`;
the constructions get `guard: None`. Then every walk over an arm's body must
walk its guard too: free variables and captures when a `match` is lifted
(`lift.rs`), automatic implicits (`autobind.rs`), the dependency and name
walks (`module.rs`), `nav.rs` (hover and go-to-definition), `numbers.rs`,
`unify.rs`, `effects.rs` (`may_perform`, effects.rs:2287), `equations.rs`
(`SourceArm`), `derive*.rs`, and `crates/driver/src/doc.rs`, `live.rs`. `grep
-n "alts\|Decl::Equation" crates/*/src` lists them; a missed walk shows up
as a guard naming something the walk didn't see (a captured variable not
passed to a lifted `match`, a definition not ordered before its user), so
the tests in §9 have a guard that names a captured variable and one that
calls another definition of the module.

## 3. Compiling

### 3.1 Where the compiler is

`Elaborator::compile` (lib.rs:3412) is a matrix compiler: `Row`s
(lib.rs:454: patterns still to match, aliases bound so far, the right-hand
side, the span) against `columns` (the de Bruijn levels being matched). It
picks the first row's first column with a constructor and splits on it
(`Tree::Case`, numbers as `Tree::NumCase`, lib.rs:3655), each branch
keeping the rows that fit, in order. When the first row has no constructor
left in any column, it matches whatever is left and becomes a `Tree::Leaf`
(lib.rs:3480-3502), and the rows below it are dropped there **[checked]**.
`compile_top` (lib.rs:3391) then annotates missing cases and reports them
together. A definition's arms reach it from lib.rs:3338-3368, a `match`'s
from `matching::compile` (matching.rs:136-186), both followed by
`warn_redundant` **[checked]**. After compiling, `check_tree` (lib.rs:4374)
checks the tree: for a `Case` it binds the fields and recurses, for a
`Leaf` it aliases the pattern variables and checks the right-hand side
**[checked]**.

### 3.2 The change

`Row` gets `guard: Option<&'a ast::Guard>`, copied wherever rows are copied
(the branch rows at lib.rs:3576, or-expansion, number arms). `Tree` gets

```rust
/// The first row matched whatever is left, under a condition: its leaf if
/// `cond` holds, otherwise `otherwise`, the rows after it here.
Guard {
    guard: &'a ast::Guard,
    leaf: Box<Tree<'a>>,          // the Leaf the row would have been
    otherwise: Box<Tree<'a>>,
},
```

In `compile`, where the leaf is made: if `first.guard` is `Some`, build the
leaf as today, then compile `rows[1..]` with the same columns and types at
(first making the splits the rows below need, §3.2), and return `Tree::Guard`. If `rows[1..]` is empty, the
`otherwise` is a `Tree::Missing` (definite, or not, exactly as an empty
branch is decided at lib.rs:3597-3625), marked as reached through a guard
for the message (§5).

**Why the splits go above the guard.** The kernel allows a `case` only at
the top of a body or of a branch (`case_only_in_tree`, core/check.rs), and
the `else` of an `if` is a lambda body, so the `otherwise` tree can't hold
one. (This note first said it could, compiled at `depth + 1` to agree with the
variable both `if` branches bind; building it showed the kernel's
`E-MALFORMED`.) So when the first row is guarded and has nothing left to
match, `compile` still splits on any column a later row needs, scanning rows
down to the first that cannot fail, and only then makes the `Guard`. Each
guard's `otherwise` is then flat: guards, leaves and missing cases. The same
holds for the leaf of every row under a guard: a `match` that is its whole
right side is lifted (checked with `guarded = true`), also for rows reached
through the `else`. A `()` nested in a later row is turned into the unit
pattern in that scan, as the first row's is. Anything else that would leave
a `case` in the `else` is `E-GUARD-ARMS`.

A missing case at the end of the chain is definite only when no column has an
indexed type; otherwise the checker tries `families::empty_case` on its
columns (in a `Case` branch, and where the chain ends), as for any missing
constructor.

`compile` today reads `rows[0]` unguarded (lib.rs:3427); an empty `rows`
can now only come from a guard's `otherwise`, which is handled before the
call, so it stays an invariant. Add a `debug_assert!`.

### 3.3 Checking a guard node

In `check_tree`, `Tree::Guard`:

1. Mark the context and alias the row's pattern variables (the leaf's
   `aliases`), as the leaf does (lib.rs:4388-4390), so `c` sees them by the
   names written. Apply the `✝` renaming of the tree's unnamed variables as
   the leaf does (lib.rs:4395-4410), so `c` can't name another arm's
   variable.
2. Call `check_if` (check.rs:4255) with the guard's binder and `cond`, and
   with the two branches given as callbacks instead of expressions:
   `then` checks the leaf (the existing leaf code, from `families::reached`
   on), `else` restores the aliases and names and checks `otherwise`. That
   needs `check_if`, `check_if_in`, `check_proof_if` and `decided_if`
   (check.rs:4543) to take the branches as something other than `&Expr`:
   an enum `IfBranch<'a> { Expr(&'a Expr), Check(&'a mut dyn FnMut(&mut Ctx,
   &Value) -> Result<Term>) }` keeps every other caller unchanged.
3. Reset the mark.

Everything `if` does then applies unchanged: a `Bool` condition, or a
decided proposition (`logic::condition`, logic.rs:125); a proof goal, so a
theorem by arms with a guard (`Decidable.elimProof`, SW-1015); the
`unused_proof_if` choice of `ifThenElse` on the decision's `Bool` when the
branches don't use the proof; the waiting decision. So "proofs see an
ordinary `if`" holds by construction: the term is the one `if c then a else
b` would make with `a` the arm and `b` the rest of the match.

**Names in the `else`.** `decided_if` binds the same name in both branches
(check.rs:4560-4561). For a guard `if h: P`, `h` is the arm's; the rows
below have their own patterns and must not see an `h` they didn't write. The
`else` binds it hidden (`_`), which `auto` still finds; `decided_if` takes the
`else` name separately. A proof below that wants the fact by name writes
`if h: P` again, which the decision settles at once.

**The arm's body under a guard** is checked inside the `then` lambda. A
`match` that is the whole body is compiled into the enclosing case tree
(`in_tree`, lib.rs:4417-4425) only when not `wrapped`, because a case split
must be at the top (the comment there) **[checked]**. Under a guard it is
not at the top, so the leaf of a guarded row is checked with `wrapped =
true`, and such a `match` is lifted, as it is under `canonical`'s `J`
today. **[estimate]**: nothing else in the leaf depends on being at the top.

**`families::reached`, `leaf_log`.** The leaf's `families::reached` and
`leaf_log.record` happen in the `then` branch. The leaf log's `path`
(pushed per branch at lib.rs:4549) gets an entry for each side of a guard,
`GUARD_THEN`/`GUARD_ELSE` constants outside the constructor range, so a
leaf's path still says uniquely where it is; stage 1 equations only need
that it doesn't collide (§6).

### 3.4 The kernel term

For

```
def clamp (limit: Nat): Nat → Nat
  | n if n <= limit => n
  | _ => limit
```

the tree is `Guard(n <= limit, Leaf n, Leaf limit)` and the term is
`ifThenElse (Nat.leq n limit) (_ => n) (_ => limit)` (the `Bool` reading of
`<=`, docs/syntax.md:1774), or `Decidable.elim (decision) (_ => n) (_ =>
limit)` if the arm used the proof **[estimate]**, from `check_if`'s rules.
After a split, the `if` is inside the branch: `| Some x if x > 0 => x | _ =>
0` is `case o of None => 0 | Some x => if x > 0 then x else 0`, with the `_`
row copied into both branches as the compiler already copies a wildcard row
(lib.rs:3562-3568) **[checked]**.

### 3.5 Code size

The compiler already copies rows: a row with `_` where another splits goes
into every branch, and `check_tree` checks a right-hand side once per leaf
it reaches (lib.rs:4377-4432, `check(cx, rhs, goal)` at every leaf)
**[checked]**. A guard adds one thing: the rows below a guarded row are kept
where they would have been dropped. In the usual shapes that costs nothing
extra (a guarded row then a fallback: one `if` per leaf of the guarded row).
The bad case is several guarded rows that split different columns:

```
| A, _, _ if c1 => …
| _, B, _ if c2 => …
| _, _, C if c3 => …
| _, _, _ => …
```

Each guarded row's `otherwise` and its sibling branch compile the same
remaining rows, so the tree doubles per such row: 2ⁿ leaves for n guarded
rows, where without guards it is linear **[estimate]**, as in [M1].
OCaml and Rust avoid it with shared continuations (static exits, jumps);
the kernel term has no join points, and sharing through a lifted helper
would change the terms proofs see. So: accept the duplication, which is
nothing for the AoC shapes (one or two guarded rows), and bound it. Count
`Guard` nodes during compilation and, past 4096, fail with `E-MATCH-SIZE`
(linear shapes, a dozen guarded catch-alls over twenty-six character arms,
make hundreds; the exponential case doubles per guarded row and passes 4096 at
the tenth guarded row; measured: nine pass, ten fail):
"this `match`'s conditions would copy its arms too many times", note
"move some of the guarded arms into a helper function, or test the
condition inside one arm". The existing `nesting` budget (lib.rs:3420)
bounds depth only.

## 4. What the arm knows

- **In the arm**, what `if c then a` gives `a`: for a decided proposition
  (`n != 0`, `x < y`), an anonymous `_: c` that `auto` uses, so `| (n, len)
  if n != 0 => len % n` checks the `%`'s proof obligation; for a `Bool`
  (`here == wanted`, `xs.isEmpty`), nothing; an `&&` chain gives the arm nothing per conjunct (`if p && q` doesn't either, on `main`).
- **Below it**, `_: Not c` in the rows' `else`, for the same conditions. In
  the bad case of §3.5 each copy knows the guards it passed.
- **By name**: `| x if h: x < n => … h …`. In a proof about a guarded
  function's result, the guard is an `if` in the unfolded term, split as
  any `if` is: `match e: c with`, `if h: c`, or the generated equations once
  stage 2 makes them.

Two things the arm doesn't know: a `Bool` guard gives no fact (as `if`
gives none; write the proposition, `n != 0` rather than `not (n == 0)`), and
an or-pattern's arm doesn't know which alternative matched.

## 5. Coverage and warnings

**E-NONEXHAUSTIVE.** A guarded row covers nothing because its `otherwise`
compiles the remaining rows; when there are none the `Missing` node is the
missing case, and `missing::definite` (missing.rs:320) reports it with the
others, annotated by `annotate` (missing.rs:168), which must recurse into
`Guard`'s `otherwise` (and `definite`'s `collect` likewise). When a missing
case was reached through a guard, add one note: "the arm at line N has a
condition (`if …`), so it doesn't count: add an arm without `if` for these
values". The other coverage checks that read rows directly ignore guarded
rows: `int_coverage` (lib.rs:4007) counts a variable as covering a sign, so
it must skip guarded rows; `compile_numbers` (lib.rs:3655) treats a
variable row as covering the default, which is right, since a guarded
variable row's `otherwise` then sees the next rows **[checked]** both.
Clause lambdas' wording (`in_context`, matching.rs:227) needs nothing:
`match some` and `matches` have their hidden last row, which is never
missing.

`| n if n < 5 => … | n if n >= 5 => …` is still `E-NONEXHAUSTIVE`, as in
Rust: the checker doesn't reason about conditions. The note above says
what to do.

**W-REDUNDANT** (redundant.rs:18): an arm is redundant when no leaf comes
from it, and leaves are gathered by `arm_spans` (redundant.rs:123), which
must collect a guard's leaf and recurse into `otherwise`. With that:

- an unguarded arm after an identical guarded one is reached (through the
  `else`): no warning, correctly;
- a guarded arm after an identical unguarded one is never reached: the
  warning, as today;
- a guarded arm after an identical guarded one is reached: no warning (the
  conditions differ, or the second is pointless, which isn't checked).

The label "this arm matches everything it does" picks the first earlier row
whose patterns subsume (redundant.rs:39-42); it must skip guarded rows,
which match nothing for certain.

**W-MATCH-TOTAL** (`never_reached_rest`, redundant.rs:80): the hidden last
arm of `match some`/`matches` is reached through any guard's `else`, so the
warning disappears exactly when a guard makes the hidden arm useful.
Nothing to change; a test pins it.

## 6. Generated equations and `f.induct`

How they are made today: each arm's equation states its left side and right
side and takes a `notArmJ` hypothesis for each earlier arm that overlaps it,
and is proved by walking the definition's kernel term with the arm's left
side, `rfl` at its leaves and `Void.exfalso` of the hypothesis at an
earlier arm's (equations.rs:1-60, `walk_proof` at 2558) **[checked]**.
`f.induct` isn't made when a case has no equation or takes a `notArmJ`
(equations/induct.rs:44-50) **[checked]**.

**What doesn't change.** A row's leaves lie where every earlier row failed;
a guard node is made only where a guarded row is first. So walking the tree
for row k meets only the guards of rows before k **[checked]** against the
compiler's construction (§3.1). Arms before the first guarded arm get the
same equations, proved by the same walk, as without guards, and a
definition with no guard gets the same terms and hashes as today: the
compiler and the checks change only when a row has a guard.

**Stage 1 (this lane).** From the first guarded arm on, no equations: each
is recorded as not generated (`skip`, equations.rs:1457) with "an arm at or
above it has a condition (`if`), which generated equations don't cover
yet", so naming one is `E-NO-EQUATION` with that reason; no `f.induct` (the
existing rule). Lifted `match` helpers (clause lambdas) follow the same
rule through their `SourceArm`s (equations.rs:3592).

**Stage 2 (a separate Opus lane).** What they should be, for the record:

- The guarded arm K: `f.eqK (vars) (notArmJ …) (guard: c = True): f lhs =
  rhs`, the hypothesis as `ifTrue`'s is for a `Bool` `if` (equations.rs
  header, stage 1b), `h: P` for `if h: P`, `guard: P` for a decided
  proposition. Proved by the walk, which at its own guard node goes into
  the `then` along the hypothesis (the `J` stage 1b uses for `ifTrue`).
- An arm L below a guarded arm J that overlaps it: `notArmJ: (vars) → x = p
  → … → c = True → Void`, Lean's form with the guard as one more premise.
  When J's patterns match everything L's do (the usual "same pattern, then
  a fallback"), it is simply `notArmJ: c[σ] = False` (or `Not P[σ]`), with
  J's variables replaced by L's terms; then nothing in `f.induct` blocks
  (it's an `if` split, `Bool.inspect`, as for branches).
- The walk recognises a guard node by the leaf log's guard entries (§3.3),
  not by the shape of the term, since an arm's own `if` looks the same.

This is the part that generates proof terms for every user of guards, so it
is Opus work, reviewed as kernel-term changes are.

## 7. Abilities in guards

A guard may not perform operations: `E-ABILITY`, "a condition after a
pattern can't perform operations", note "run it before the `match` with
`let`, or test it inside the arm". Reasons: `if h:` already refuses
(effects.rs:2751-2757); a guard runs once per alternative of an or-pattern,
and in an effectful one that would show; and the case tree would have to
sequence a computation in the middle of a match, which `check_tree` doesn't
do (effects run a `match`'s scrutinees first, effects.rs:2771-2800, and the
arms are checked against the computation type) **[checked]**. The test is
the one `if` uses: `may_perform(cond)` and not `performs_nothing(cond)`
(effects.rs:2745). So `| xs if xs.all (x => x > 0) =>` is fine,
`| x if ask() == x =>` isn't. The arms themselves may still perform what
the expected type allows, and a pure guard in an effectful `match` works,
since `check_if` checks both branches against the computation type, as for
an `if` with a pure condition (effects.rs:2745-2748) **[estimate]**: a test
covers it. Allowing effects later is a compatible change.

## 8. AoC sites

partial-lambdas.md §3 lists five; on a closer look two gain and three don't:

| Site | Today | With a guard | Migrate? |
| --- | --- | --- | --- |
| 2024 day 15 `positionsOf` (Day15.sw:57-60) | `.filter (((position, here)) => here == wanted) \|> .map ((((row, column), here)) => …)` | `.filterMap (match some \| ((row, column), here) if here == wanted => …)` | yes: one step, the pair taken apart once |
| 2021 day 18 `orderedPairs` (Day18.sw:110-112) | `.filterMap (((j, y)) => if i == j then None else Some (x, y))` | `.filterMap (match some \| (j, y) if j != i => (x, y))` | yes, and adjust `memberPairs`/`pairsMember` (Proofs/Answers.sw:64-80), which split `i == j` |
| 2024 day 6 `positionsOf` (Day06.sw:52) | `cells.filter (.snd == wanted) \|> .map .fst` | `cells.filterMap (match some \| (position, here) if here == wanted => position)` | no: the sections are shorter |
| 2024 day 20 `onlyTile` (Day20.sw:45) and the track (Day20.sw:57) | the same sections | as day 6 | no |
| 2024 day 16 `onlyTile` (Day16.sw:38), not in the note's list | the same | as day 6 | no |

The day 18 change is the proof example: the proofs go from `match e: i ==
j` on the old `if` to splitting the guard in the lifted helper.

## 9. Tests

Examples under `examples/accept` and `examples/reject` (`-- expect-error:
CODE` on the first line), run with `task test:one -- NAME`:

- **accept** `pattern-guards.sw`: a guard in each form (`match … with`,
  definition arms, `match | …`, `match some | …`, `matches | …`, `:= match
  some | …`); one-line arms; an or-pattern with a guard; a two-pattern arm;
  a guard naming a captured variable inside a lifted `match`; a guard
  calling a definition declared below it; `#eval`s showing the fallthrough
  (a guard false, the next arm taken; `match some` giving `None`).
- **accept** `pattern-guard-facts.sw`: `| (n, len) if n != 0 => len % n`
  (the arm knows `n ≠ 0`); a later arm using `Not c` through `auto`; `if h:
  x < n` with `h` used in the arm.
- **accept** `pattern-guard-proofs.sw`: `clamp` (§3.4) with `theorem
  clampLe (limit n: Nat): clamp limit n <= limit` by `match e: n <= limit
  with`; a `match some` with a guard and `List.memFilterMap` about it; a
  guarded arm in a theorem (a proof goal, `elimProof`).
- **accept** `pattern-guard-effects.sw`: a pure guard in a `{Fail}`
  function's `match`; a guard calling `List.all` with a pure callback.
- **reject**: `pattern-guard-nonexhaustive.sw` (`E-NONEXHAUSTIVE`, with the
  note; also the `n < 5` / `n >= 5` pair), `pattern-guard-redundant.sw`
  (`W-REDUNDANT` as an error-free warning test, if the harness checks
  warnings that way; otherwise a driver test), `pattern-guard-ability.sw`
  (`E-ABILITY`), `pattern-guard-absurd.sw` (`E-PARSE`),
  `pattern-guard-in-handler.sw` (`E-PARSE`), `pattern-guard-size.sw`
  (`E-MATCH-SIZE`, thirteen guarded rows on different columns).
- **W-MATCH-TOTAL**: `match some | Some x if x > 0 => x` doesn't warn;
  `match some | x => x` still does.
- **Unit tests** in the parser (as `clause_lambdas_are_lambdas_over_a_match`,
  parser.rs:6110): the guard's span and binder; `| x if flag => e` isn't a
  lambda; `| x if xs |> f => e`; the guard over an or-pattern.
- **Equations (stage 1)**: a definition with an unguarded arm, a guarded
  one, and a fallback: `f.eq1` exists and is unchanged, `f.eq2` is
  `E-NO-EQUATION` with the reason.
- **Unchanged hashes**: the hash snapshot tests for files without guards
  must not move; run the snapshot test for the std and AoC files touched
  only (the merge tier covers the rest).

## 10. Plan for the implementer

Sizes are [estimate]; the whole is the ticket's 3-4 hours.

1. **Syntax** (45-60 min). `ast::Guard`, the fields, `guard_start` and the
   stop, `guard?` in `match_expr`, `clause_lambda`, definition `arm`, the
   `:= match` lowering, `KwIf` in the constructor stop set, the absurd-arm
   error, the equivalence check, and every walk in §2.5. Parser unit tests.
   `stitchwort fmt` round-trips the new examples.
2. **Compiler and checking** (60-90 min). `Row.guard`, `Tree::Guard`,
   splitting for the rows below before the condition, the empty-`otherwise` `Missing`, the size
   bound, `check_tree`'s guard node with the `check_if` branch callbacks
   and the hidden `else` name, `wrapped` for guarded leaves, leaf-log path
   entries, `annotate`/`definite`/`arm_spans`, `int_coverage`, the
   redundancy label, the `E-ABILITY` check.
3. **Equations, stage 1** (15 min). The skip from the first guarded arm,
   and its test.
4. **Tests and docs** (30-45 min). §9's examples; docs/syntax.md's `match`
   section, a paragraph on guards with the examples named; a line in
   partial-lambdas.md §6 pointing here.
5. **AoC** (30 min). Day 15 and day 18 (§8), with day 18's proofs; check
   each day as its tests are run (`task test:one`).

**Risks.**

- *The `else` tree* (step 2): no `case` can sit in it (§3.2), so the splits
  the rows below need are made above the condition, and every leaf under a
  guard is checked as guarded. Test an arm below a guard whose right side is
  a `match`, and indexed families, where the failed-guard case may be
  impossible.
- *A missed walk* (step 1), §2.5: found by the capture and ordering tests.
- *`check_if` refactor* (step 2): it is used everywhere; the enum keeps its
  callers' code unchanged, and the existing `if` examples
  (`examples/accept/if-*.sw`, by name with `task test:one`) cover them.
- *Equations, stage 2*: not in this lane (§6); Opus.

## Sources

- [M1] Luc Maranget, "Compiling pattern matching to good decision trees"
  (ML Workshop 2008): guards as tests whose failure continues with the
  remaining rows. From memory, **unverified**.
- Rust reference, "Match guards": a guard may run more than once with
  or-patterns; guarded arms don't count for exhaustiveness. From memory,
  **unverified**.
- OCaml manual, `when` guards in `match`. From memory, **unverified**.

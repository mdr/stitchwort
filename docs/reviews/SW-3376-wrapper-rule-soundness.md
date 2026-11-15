# SW-3376 (recursion-through-map stage 1a): soundness review of rule 3, the one-field wrapper

**Reviewed:** branch `lane/SW-3376` at `0c4dc20e3` (`git diff main...lane/SW-3376`):
`crates/core/src/termination.rs` (`Info::parent`, `Walker::wrapped`, `part_of`,
`strictly_inside`, and their use in `relate`), `docs/core.md`, the new examples. Paper review by
Fable, 15 November 2026, for D3613. **[run]** means probed with the lane's release binary
(`check --no-cache` or `test --no-cache` on scratch files, about 0.3 s each); **[run, main]**
means also run with the main checkout's binary; **[argued]** means reasoned from the source and
`docs/core.md`. No suites, no builds. Probe files are in
`/private/tmp/claude-550/-Users-agent-repos-mdr-stitchwort/8230e28a-2fab-4832-920d-c5160adb7e00/scratchpad/sw3376rev/`
(`p01.sw` to `p12.sw`); the ones worth keeping are quoted below.

## 0. Verdict

**Sound.** I found no program the new code accepts that fails to terminate on closed inputs, none
that makes the kernel's evaluator or conversion unfold without end on open terms, and no route to
`False`. Nothing has to change before merging.

Three things should be fixed in the text or hardened, none of them a hole today:

| # | Finding | Kind | Severity |
|---|---|---|---|
| F1 | The stated open-term argument ("the match from `v` to `u` is stuck") is false for some accepted programs; the property holds for a different reason | Wrong argument in `termination.rs`, `docs/core.md` is silent, proposal §3 | Medium (documentation of a kernel invariant) |
| F2 | "A rebuilt constructor is equal" and "an inlined parameter equals its argument" are false at proof positions: the checker records a false `<`. Not exploitable, because of two positivity rules nobody has tied to termination. Already on `main` | Unstated dependency, pre-existing | Medium (a hole if either positivity rule is ever relaxed) |
| F3 | `wrapped` doesn't refuse a `C` whose one field is a recursive function field; it can't fire there today, but only by accident of what `strictly_inside` can follow | Hardening | Low |

## 1. What the code does, checked against the rule

`relate` on a constructor tries `rebuilt` and, if that gives no relation, `wrapped`. `wrapped(C
u)` needs: one argument and a one-field `C` (all fields count); `part_of(u)` a variable (`u`
itself, a rebuilt constructor's variable, or the field variable of a recursive function field
applied); an enclosing match `m` on the same data type and constructor; and `strictly_inside`:
from that variable, following `parent` (set only by `case`, resolved through an inlined
parameter's `alias`) one or more times, reaching `m`'s field. The result is `<` the parameter
`m`'s scrutinee is `≤` or `<`.

I read each path for a way to make a false statement:

- `parent` is set only in the `Case` arm of `walk`; `Let`, `Lam`, `Pi` and `inline` leave it
  `None`. A chain therefore stops at a `let`, a lambda's variable, and an inlined parameter whose
  argument isn't a variable or rebuilt constructor. **[checked]**
- An alias never points at an aliased variable (`rebuilt` resolves on creation), so one `resolve`
  step is enough. **[checked]**
- Levels are stable: `vars` and `matched` are both stacks, and an inlined body is closed over its
  own parameters, so no level in `matched` or `parent` can refer to a popped variable.
  **[checked]**
- `find_map` skips a match whose scrutinee has no relation and goes on outwards; any match that
  qualifies gives a true statement, so which one is found first doesn't matter. **[checked]**
- `rebuilt` first: if it gives `≤` or `<`, that is used; `wrapped` only adds `<` where `rebuilt`
  gave nothing. The two can't disagree in a harmful way, since each is a true statement about a
  possibly different variable. **[checked]**
- A zero-field constructor (`[]`) is "rebuilt" as the innermost enclosing variable matched as
  that constructor. That is a true equality, and `MkW []` is then smaller only if that variable
  is strictly inside `v` (`h6`, `h6b`, `h6c` below). **[run]**

## 2. Closed programs: the rank argument

The header's argument is right, and can be said without sets. Let `≺` be the relation the
existing rules generate on closed values (a field of a constructor; a declared recursive function
field applied), well founded by the assumption the check already makes, and `ρ` its rank
(`ρ(x)` = the least ordinal above `ρ(y)` for every `y ≺ x`). For a constructor `C` whose one
field is not a recursive function field, the only `≺`-predecessor of `C v` is `v`, so `ρ(C v) =
ρ(v) + 1` exactly, whatever types `C v` and `C u` have. So `u ≺⁺ v` gives `ρ(C u) < ρ(C v)`, and
adding rule 3's pairs keeps `ρ` a rank. Types never enter, which is why a different instance of
the field type (`W (List (List a))` to `W (List a)`), an indexed `C`, a `C` in `Prop`, or a proof
or erased field as the one field change nothing. (F3 is the one condition this needs that the
code doesn't state.)

## 3. Attacks and outcomes

### 3.1 The lane's four weak points

**(1) `C`'s field type a type parameter; another instance; is "the match on `v` stuck" still
true?** No, and this is F1. The claim fails, the property survives.

```
type P (a: Type) (b: Type) = { fst: a, snd: b }
type R (a: Type) = { only: a }
type TEq (a: Type): Type → Type 1 = | TRefl: TEq a a

def f (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat) (w: R (t n)): Nat :=
  m t es n (t n) (t (Succ n)) (es n) TRefl w

def m (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat) (a: Type) (b: Type): (e1: TEq a (P b Nat)) → (e2: TEq b (t (Succ n))) → (w: R a) → Nat
  | TRefl, TRefl, w => m2 t es n w

def m2 (t: Nat → Type) (es: (n: Nat) → TEq (t n) (P (t (Succ n)) Nat)) (n: Nat): (w: R (P (t (Succ n)) Nat)) → Nat
  | { only = { fst = x, snd = y } } => f t es (Succ n) { only = x }

theorem z (t …) (es …) (n: Nat) (w: R (t n)): f t es n w = 0 := rfl
```

**[run]** (`p07.sw`): accepted on the branch (refused on `main`). The descent is rule 3: `{ only
= x }` with `x` inside the matched `only`. Both `R` and `P` have record eta, so *neither the
match on `C` nor any match from `v` to `u` is ever stuck*: on an unknown `w` they all take their
branch with projections. The only thing that stops the kernel unfolding `f t es n w` for ever is
the `case` on the type equation `es n`, which is outside the chain the rule looks at. `z` fails
in 0.27 s with "the left side is stuck on `es`", so evaluation does stop.

It is not a new exposure: the same program without the wrapper (`f … (v: t n)`, `m2 | { fst = x
} => f … x`) is accepted by `main` today **[run, main]** (`p12.sw`). Rule 3 only puts `C` on both
ends.

Why it always stops **[argued]**: give every open value a size `μ`: a constructor is one more
than the sum of its fields; an unknown of type `A` is `A`'s *eta depth* (1 + the sum over the
fields' types if `A` is an eta record, else 0). Eta depth is finite because eta records are not
recursive (condition 3 of "Record eta") and types in any context are finite: equations between
types enter a context only through index unification, which solves variables with an occurs
check and never takes a type former apart (`E-INDEX-STUCK`), and `J` on an unknown proof is
stuck. A `case` that fires takes `μ` strictly down (it eats a constructor, or one eta layer of
an unknown), and `μ(C u) = 1 + μ(u) < 1 + μ(v) = μ(s)` whether `s` was a constructor or an
unknown of an eta type. So each turn of an accepted cycle lowers `μ` of the value on the thread,
or is stuck. I tried to get an unbounded eta depth and couldn't: a type function that unfolds
without a `case` (`Tower n := P (Tower' n) Nat`, `Tower'` by cases) leaves `Tower' n` stuck; a
cyclic hypothesis `TEq a (P a Nat)` fails the occurs check; a stream of equations (`es` above) is
stuck at each one; the `castViaBox` subject-reduction gap (proof-irrelevance.md §5.7) only casts
between `f p` and `f q` for two proofs of one proposition, and a type computed from a proof needs
`E-PROP-ELIM`'s rule that the proposition doesn't mention itself (D1980), which bounds it too.

Other instances of `a` **[argued, some run]**: a function type (nothing can be matched out of
`v`; a field of declared type `a` is never a recursive function field, so `h 5` is unknown,
`termination.rs:375`); `Type` or a universe (not matchable); a one-field record with eta (`Path`,
`Age`, `R` above: `a1`-`a6`, `o6` stop **[run]**); a unit-like record (no eta, condition 4, so
its match is stuck); an indexed family (`S (length l)`, `Wv n` around a `Vec`: accepted, honest
**[run]**); a large elimination (must match the index first, and that match is stuck). There is
no universe polymorphism to try.

**(2) Does `alias` mean an equal value?** Up to proofs only: F2. Otherwise yes: an alias comes
from `rebuilt`, and a field pinned by a later field's type is definitionally equal to the matched
one, so equal in every run except inside proof positions.

**(3) A recursive function field as `C`'s only field.** `type Tr = | Leaf | Sup (kids: Nat →
Tr)`: nothing is strictly inside a function, so `Sup (n => kids (n + 1))` and its `W`-wrapped
form are refused **[run]** (`d3b`, `d3c`, `d3d`; all three would loop). `MkW (kids 0)` after
`MkW (Sup kids)` is accepted and honest **[run]** (`d3`). See F3.

**(4) `rebuilt` first.** No effect on soundness (§1). `MkText [c, ..cs]`, `MkW []` in the `[]`
branch and `MkWv (VCons x (VCons y rest))` all come out "stays the same" **[run]**.

### 3.2 The rest of the brief's list

| Attack | Outcome |
|---|---|
| Mutual group: `e3 (MkW [_, ..r]) = e4 r; e4 r = e3 (MkW [0, 0, ..r])` | Refused **[run]**; the honest `e1`/`e2` pair accepted |
| Nested matches on one variable twice (`c1`) | Accepted, honest; each field variable's chain reaches only its own match's field **[run]** |
| Shadowing: `MkW v => apply v (v => match v …)` | Refused **[run]** (`c3`); levels, not names |
| `let big := [0, 0, ..v]` then match; match on `grow v`; match on `[0, 0, ..v]`; tuple scrutinee with the other list | All refused **[run]** (`c5`, `c4`, `c6`, `c7`) |
| `let t := r; f (MkW t)` (honest) | Refused, as documented: a `let` breaks the chain **[run]** |
| A part of another parameter (`b7`); growing one wrapper while shrinking the other (`b9`) | Refused **[run]**; the honest swap `b8` accepted and runs |
| `MkRose` (one-field, recursive, nested): `MkRose rest` accepted; `MkRose [k, k, ..rest]`, `MkRose [k]` refused | **[run]** (`r1`-`r3`); `MkRose [k]` could be the parameter itself |
| Wrapper in a wrapper, `MkW (MkW r)` | Refused (conservative: the inner `MkW r` is not a variable) **[run]** |
| Text: `"" ++ rest`, `"a" ++ rest` rebuilt, a longer text | Refused **[run]** (`k1`-`k3`); nested prefix matches and `rest` under a lambda accepted, run, and stop on an unknown text (`k4`, `k5`) |
| Implicit sole field `MkI [xs := r]` | Accepted, honest **[run]** |
| Open terms: `rfl` against `0`, against a renamed copy, under a binder, on `Rose`, `W Tr`, `Age`, `Path`, `Text` | Every one answers in 0.3 s (2 s for the file of `Text` probes), none `E-RESOURCE` **[run]** (`a1`-`a6`, `o1`-`o6`, `k5open`) |
| `decreasing` | No interaction: its recursive calls are `%rec`, a lambda's variable, and `f.%go` descends on fuel **[argued]** |
| Codata, `Effect.Delay`, quotients | Not matchable, so never on a chain **[argued]** |
| Proof irrelevance | Only through F2. Comparison skips proofs; evaluation never swaps one, and a `case` on an unknown proof is stuck in the kernel **[argued]** |
| Proofs into data through the wrapper | `E-PROP-ELIM` (one constructor, proof fields only, no self-mention) still applies to every `case` on the chain; `theorem d2: WP → Big` by rule 3 on a proof field is accepted and honest **[run]** |
| Natives, opaque definitions | The check runs on the body as before; a native's agreement with its body is trusted separately, unchanged **[argued]** |
| Erased runs | A `case` on an erased proof takes its branch without a value, like eta; the same typing argument bounds it, and D1980 is what rules out the recursive case **[argued]** |
| Hash and check cache | Acceptance isn't stored or hashed. A cached entry skips the termination check (`admit_trusted_group`), but the cache key holds the build fingerprint, which covers every source file of the driver's crate graph including `crates/core` (`crates/driver/build.rs`, `fingerprint::check_crates`), so no entry written by another checker is ever replayed **[checked]** |

## 4. Findings

### F1. The open-term argument is stated wrongly (medium; text only)

`termination.rs:71-77`: "every accepted cycle crosses a `case` on a type without eta whose
scrutinee is the evidence's variable … A one-field constructor around a strict part keeps this
because it needs the matches from `v` down to `u`". The proposal (§3: "the match from `v` to `u`
is stuck on an unknown `v`") and the SW-3359 review (§1: "a type with eta can't be recursive, so
getting from a value back to a value of its own type crosses a `case` on a type without eta") say
the same. §3.1 (1) is an accepted program where every match on the chain has eta; the last
argument silently assumes the callee's parameter type is the same at every call, which
recursion at a changing type breaks. `main` has the same gap for plain fields.

**Fix:** replace the paragraph with the `μ` argument of §3.1 (a `case` that fires lowers the
size of an open value, counting an unknown of an eta record type as its finite eta depth), and
say what it rests on: eta records are not recursive, index unification never solves cyclically
or takes a type former apart, and D1980. Put the same sentence in `docs/core.md`'s "Unfolding
policy" bullet, which currently says only "That makes conversion terminate". This matters for
stage 1b and 2: G1 is argued from "a root `case` on a type without eta", and whoever writes that
argument should start from the true invariant. Optional belt and braces: under the `reference`
feature, when `wrapped` fires, assert that some `case` on the chain or enclosing the call is on
a type without eta; `p07.sw` shows the right place to look is *any enclosing case*, not the
chain.

### F2. A false `<` at proof positions, harmless because of two positivity rules (medium; pre-existing)

```
type Big: Prop = | Stop | More (b: Big)
type PBox (p: Big): Type = | MkPBox
type T: Type = | Mk (p: Big) (x: PBox p) | In (t: T)

theorem viaAlias: T → Big → Big
  | Mk p x, b => (match Mk (More (More p)) x with
      | Mk w y => viaAlias (Mk w y) w
      | In t => Stop)
  | In t, b => viaAlias t b
```

**[run, main]** (`p10.sw`): refused, but with "the 2nd argument is smaller than the 1st
argument was". `w` is `More (More p)`, which is *bigger* than `Mk p x`. `rebuilt` lets a field
pinned by a later field's type be any term because typing forces it equal; `PBox`'s parameter is
a proof, which comparison skips (`Data::proof_params`), so `Mk (More (More p)) x` type-checks and
is taken for the matched value; the inlined match's parameter gets it as `alias`, and its fields
are recorded as parts. The same happens for a pinned data field with a proof nested in it. With
rule 3, `MkW (Mk (More p) x)` after `MkW (In (Mk p x))` is accepted as smaller this way
**[run]** (`d1`; it does terminate).

So the header's "a rebuilt constructor is equal" is true only up to proofs, and the checker's
relation is not rank-monotone for theorems that recurse on proofs. I could not turn this into a
loop or a proof of `False`, and I believe it can't be done **[argued]**: the swapped part is
always a proof-position component of a pinned field; that field's type can't mention the type
being matched or its group, directly (`E-POSITIVITY`, "no field depends on one holding `D`":
`Mk (p: Big T) (x: PBox T p)` is refused **[run]**, `p09.sw`) or through nesting (nestable
condition 5: `Node (q: Q T)` with `Q a = MkQ (p: Big a) (x: PBox a p)` is refused **[run]**,
`p11.sw`). So a size-change thread that uses a false arc lands in a value that can never lead
back to a place where another false arc starts, and from there every arc is honest. Rule 3
preserves this: `C u` has `C v`'s type constructor.

**Fix (small, for a follow-up ticket, not this lane):** state in `termination.rs`'s header and in
`docs/core.md` that "equal" means equal up to proof positions, with this argument, and that the
termination check therefore *depends on* those two positivity rules; add `p09`, `p10`, `p11` as
tests so that relaxing either rule fails a termination test. If a cheaper guarantee is wanted,
make `pins_var` ignore proof-parameter positions (it removes the direct case, not the nested
one).

### F3. `wrapped` should refuse a recursive function field as the one field (low; hardening)

§2's `ρ(C v) = ρ(v) + 1` needs `C`'s field not to be a recursive function field (for `Sup kids`
the rank is the supremum over the results, not `ρ(kids) + 1`). Today the rule can't fire there
only because nothing is "strictly inside" a function. Stage 1b and 2 add new ways to be inside
something. **Fix:** in `wrapped`, return `None` when `is_recursive_fn` holds for `C`'s field
(two lines), and say so in the rule's wording.

## 5. Tests to add

To `examples/` (each is a few lines; sources in the scratch files named):

- **accept** `termination-wrapper-changing-instance.sw` (`p07.sw`), with a comment that its only
  stuck match is on the type equation, plus a driver test that `f t es n w` on unknowns is stuck
  on `es` within a small budget. This is the regression test for F1's invariant.
- **accept** with tests: `c1` (same variable matched twice), `c2` (match on the field under a
  lambda), `b8` (two wrappers swapped), `d3` (`MkW (kids 0)`), `d5`/`d6` (indexed wrapper, `Vec`
  inside), `d10` (implicit sole field), `r1` (`MkRose rest`), `halve` (`{ years = k }`), `h6c`
  (`MkW []`), `d2` (a theorem through a proof field).
- **reject**: `c3` (shadowing lambda), `c4` (match on a function's result), `c5` (match on a
  grown `let`), `c6` (match on `[0, 0, ..v]`), `b7` (a part of another parameter), `b9`, `e3`/`e4`
  (growth through a second member), `h6b` (`MkW []` when the list is `[]`), `r2`, `r3`, `d3c`,
  `d3d` (shifted function field), `d6b`, `d6c`, `k1` (`"" ++ rest`), `k2`.
- **F2**: `p09`, `p10`, `p11` as reject examples, `d1` as an accept example whose comment says
  what is being relied on.
- **Open terms** (P2 of the SW-3359 review, small version now): for each accept example above,
  `rfl` of the call on unknowns against `0` fails with `E-REFL`, never `E-RESOURCE` (`a1`-`a6`,
  `o1`-`o6`, `k5open` are ready-made).
- A unit test for F3 once the guard is in.

## 6. Not done

No test suites, builds or fuzzing; no change to the branch (this file is uncommitted). The `μ`
argument and F2's "can't lead back" argument are on paper, not mechanised. I did not review the
elaborator's side of prefix patterns (`let rest := MkText r`), the error wording, or the guide
text beyond reading them. Stage 6's properties P1 and P2 (generated programs run under a budget;
read-back under a budget) remain the right mechanical check for both arguments.

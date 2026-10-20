# `calc` chains and a `rewrite` term (SW-99), draft 4

**Date:** 19 October 2026. **Ticket:** SW-99 (related: SW-26). **Decisions:** D32 to D42.
**Status:** reviewed once externally ("adopt with changes"; no critical findings). D32 to D42
accepted by Matt on 20 October 2026. `calc` is built (SW-136, D46). A second external review
of draft 3 (D47) found no critical issue and said: implement `rewrite` once two changes are
made to §6. Draft 4 makes them. `rewrite` (stage 2) is built (SW-153); see
[As built](#as-built-stage-2-sw-153) for what differs from the text above.

## Changes since draft 3

The second review (of draft 3) found the first review's findings adequately resolved and no
unsoundness. Its findings were two major and one minor, plus a wording nit:

1. **A round-trip check after abstraction** (major; §6.2, §6.3, §9).
   - The search abstracts a matched candidate `c` to build the motive `M`, but `M a` (with
     the rule's left side `a`) was assumed to be convertible to the original goal `G`.
     That holds when conversion is congruent.
   - The proof-irrelevance proposal's D1′ deliberately isn't congruent there. It equates
     `MkBox p` with `MkBox r` by masking the proof field, while `Box.unbox` can still tell
     `p` from `r`. So a match can produce a `J` the kernel rejects.
   - The kernel still catches this, so it is never unsound, but it would be a confusing
     failure. Now, after abstraction, `M a ≡ G` is checked explicitly, even for matches found
     by the syntactic fast path. Failure is `E-REWRITE-MOTIVE` with its own explanation.
   - §9's claim that proof irrelevance would "remove" the differing-proofs problem is toned
     down.
2. **"First occurrence" is now defined** (major; §6.2, §7).
   - The search is pre-order (outermost first), left to right.
   - Once a candidate is selected, the search doesn't look inside it, so matches never
     overlap. This is what Lean's `kabstract` does.
   - So "the first match fixes the rule's implicit arguments" has a precise meaning. Two
     tests pin it down.
3. **Transactions cover the whole candidate attempt** (minor; §6.2).
   - The saved state is taken before the carrier-type check, step 3, which can itself
     constrain rule metavariables.
   - The shared budget is *not* rolled back, because failed candidates still did work.
   - Caches that depend on metavariable assignments are part of the transaction or are
     invalidated.
4. **Wording** (§6.1). An argument named `in` is written in parentheses, not "brackets".

The second review's answers to §11's questions are summarised at the end of §12.

## Changes since draft 2

Draft 2 had one external review. Its verdict was "adopt with changes", with no critical
findings, four major and three minor. Every finding is addressed below. The review's answers
to the nine questions are summarised in [Review answers](#12-review-answers).

1. **Proofless `calc` steps** (major; D33; §5.1, §5.2, §9).
   - A step with no proof is now defined as "check `rfl` against the step's proposition
     `e(i-1) R ei`".
   - Draft 2's "the endpoints are convertible" was right only for `=`. Under the new rule,
     `calc 0` / `_ <= n` is accepted, because `Nat.leq 0 n` computes to `True`, and
     `calc n` / `_ < n` is rejected **[checked: the same propositions proved by `rfl`]**.
2. **Running out of budget is inconclusive, not "no match"** (major; D36; §6.2, §6.3).
   - One rewrite-search budget is shared by every comparison in a `rewrite`.
   - If a plausible candidate exhausts it, the result is `E-REWRITE-BUDGET`, never a silent
     skip.
3. **Metavariables in a rule** (major; D36; §6.1, §6.2).
   - Matching is transactional: each candidate attempt saves the metavariable state and
     restores it on failure.
   - It is one-way: only the rule's own metavariables may be solved, never ones already in
     the goal.
   - A rule whose left side has a metavariable at its head is rejected. Lean checks exactly
     this, `lhs.getAppFn.isMVar`; draft 2 described Lean's check as "the left side is a
     metavariable".
4. **Typed matching** (major; D36; §6.2).
   - Before comparing a candidate with the rule's left side by conversion, its type is
     checked against the equation's type.
   - The kernel's comparison is untyped, and the proof-irrelevance proposal's option D1′
     requires every comparison to be between values of one type (§6.2).
5. **The chain's relation is the fold of the composition table** (minor; D34; §5.3), not a
   separate "strongest wins" rule. For today's three relations they agree.
6. **`rewrite p` without `in`** (minor; D35; §6.1). It is `rewrite p in rfl` against the whole
   current proposition. That is any relation, and both sides.
7. **Rocq's occurrence behaviour** (minor; §4.5). The review said current Rocq replaces only
   the first occurrence by default.
   - The current Rocq documentation does say "If not specified, only the first occurrence in
     the conclusion is replaced". The same page also says "Only subterms identical to that
     first matched subterm are rewritten".
   - I ran Rocq 9.1.1 to settle it. `rewrite H` with `H: a = b` turned `a + a = b + b` into
     `b + b = b + b`: every copy of the first-matched instance was replaced. With a
     quantified `H: forall n, n + 0 = n`, it rewrote `a + 0` but left `c + 0`
     **[checked]**.
   - So draft 2's description stands, now marked checked, with both documentation sentences
     quoted.
8. **Syntax** (D35, D39; §6.1, §9).
   - `in` becomes a *contextual* keyword, as `auto` already is.
   - Comma lists apply left to right, stated explicitly.
   - Only `calc` is reserved in stage 1; `rewrite` is reserved in stage 2.
9. **Stage 2 records metrics** (§9): candidates tried, conversion calls, evaluation steps,
   cache hits.
10. **New §7, "What will surprise users"**: the review's list, plus the `windowZero` case.
11. **Decisions** (§13) now show the reviewer's verdict next to each recommendation.

## Contents

- [0. The short version](#0-the-short-version)
- [1. Background: Stitchwort in brief](#1-background-stitchwort-in-brief)
- [2. The problem, with real examples](#2-the-problem-with-real-examples)
- [3. Terms used](#3-terms-used)
- [4. How other languages do it](#4-how-other-languages-do-it)
- [5. `calc` for Stitchwort](#5-calc-for-stitchwort)
- [6. `rewrite` for Stitchwort](#6-rewrite-for-stitchwort)
- [7. What will surprise users](#7-what-will-surprise-users)
- [8. SW-26: the existing `match h: e with` already solves it](#8-sw-26-if-case-splits-the-existing-match-h-e-with-already-solves-it-d40)
- [9. Implementation sketch, staging and risks](#9-implementation-sketch-staging-and-risks)
- [10. Effect on proof size](#10-effect-on-proof-size)
- [11. Questions for the reviewer (draft 2)](#11-questions-for-the-reviewer-draft-2)
- [12. Review answers](#12-review-answers)
- [13. Decisions](#13-decisions)
- [As built (stage 2, SW-153)](#as-built-stage-2-sw-153)

Labels used below:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked documentation or source;
- **[inferred]**: my reasoning from checked facts.

## 0. The short version

Stitchwort proofs are terms, and every equality step is written by hand as
`Eq.trans (Eq.cong (\x => …) lemma) …`. The `\x => …` (the *motive*, §3) repeats the whole
expression around the part that changes. The Advent of Code (AoC) proofs for days 1 to 3
contain 81 such hand-written motives and 11 `Bool.inspect` case splits with hand-written
motives (§2).

This note proposes two additions. Both elaborate to the terms written today (`Eq.trans`,
`J`, `Nat.leTrans`), so the kernel doesn't change.

1. **`calc`**: a chain of steps, one per line, where each line states the next expression
   and a proof that it follows. This is the same idea as Lean's `calc`, Agda's
   `begin … ≡⟨ p ⟩ … ∎` and Dafny's `calc`. It allows `=`, `<=` and `<` on `Nat` in one
   chain, and it fills in the arguments of `Nat.leTrans` itself.
2. **`rewrite p in t`** (and `rewrite p` alone, which closes the goal with `rfl`). The motive
   is found by looking for the left side of `p` in the goal and replacing it. This is the
   mechanism of Lean's `rw`/`▸`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's
   `rewrite`. Occurrences are found by typed, keyed matching (§6.2).

Measured on five real lemmas (§10):

- `rewrite` alone makes them 31 to 45% shorter.
- `calc` makes them about as long as now, and sometimes longer. Every intermediate
  expression is written out and checked, so a reader can follow the proof line by line.
- `calc` is 29% shorter on the `<=` chain, because it fills in `Nat.leTrans`'s arguments.

**SW-26 needs neither.** The existing `match h: e with` already does Agda-style
*with-abstraction*. I replaced six of the 11 `Bool.inspect` proofs with it, and they all
check **[checked]**:

- day 3: `pickGe`, `pickLen`, `pickSub`;
- day 2: `gaussPick`, `windowZero`, and the nested split in `window`.

Day 2's `IsTrue`/`decIsTrue` helpers become unused and are deleted (§8).

Recommendation: build `calc` first (stage 1, small), then `rewrite` (stage 2, medium). Close
SW-26 by moving the AoC proofs to `match h: e with`. The decisions are in §13.

## 1. Background: Stitchwort in brief

Stitchwort is a strict, pure, total and dependently typed language, written in Rust. Its main
use is writing library functions, proving things about them, and calling them from a
JavaScript or TypeScript application. Proofs are ordinary terms: there is no tactic language
(DESIGN.md §6, "No tactics"). The compiler also runs in the browser as WebAssembly.

### 1.1 The kernel

A small kernel re-checks everything the elaborator produces.

- It decides definitional equality ("conversion") by evaluating both sides to values and
  comparing them (normalisation by evaluation).
- The comparison is *untyped*: "it's handed two values and never told their types"
  (`docs/proposals/proof-irrelevance.md`).
- Definitions are unfolded lazily: "a definition stays folded (a neutral `Def` head) until it
  has all its parameters *and* its case tree can take a step" (`crates/core/src/value.rs`,
  module comment).
- Equality is built in. `a = b` is a proposition, `rfl: a = a` its only constructor, and `J`
  its eliminator. The rule (`docs/core.md`) is: if `p: x = y` at type `A`, and the motive `P`
  is written `\y' p' => T` with `y': A` and `p': x = y'`, then `J P d p` needs `d: P x rfl`
  and has type `P y p`. `J P d rfl` computes to `d`; with any other proof it's stuck.
- There is no axiom K and no definitional proof irrelevance: "two different proof terms
  aren't automatically equal" (`docs/core.md`). There is no function extensionality.
- `Prop` is a universe of erased propositions. `theorem` is a definition whose type is in
  `Prop`.

### 1.2 The elaborator

The elaborator turns surface syntax into kernel terms. It is bidirectional:

- `check(e, T)` elaborates `e` against a known expected type `T`;
- `infer(e)` elaborates `e` and computes its type.

Implicit parameters, written `[x: A]`, are inserted as metavariables and solved by
unification (`crates/elab/src/check.rs`, module comment). The output is always re-checked by
the kernel, so elaborator bugs can reject programs but can't make the kernel accept a wrong
proof.

**`auto` parameters.** `[auto ok: P]` asks the compiler to find a proof of `P`. It tries, in
order (DESIGN.md §6, "`auto` and `Decidable`"):

1. evidence supplied explicitly;
2. a hypothesis in scope whose type matches;
3. a registered decision procedure, run at compile time.

The proof from a decision procedure is built as `Decidable.fromYes d Trivial`, which "only
checks when `d` computes to `Yes`" (`prelude.sw:211`). Division needs one:

```
def Nat.div (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := Nat.divFuel n n d
def Nat.mod (n: Nat) (d: Nat): [auto ok: d != 0] -> Nat := n - (n / d) * d
```

So every `x % d` in a goal carries a proof term about `d`.

`auto` is a *contextual keyword*: it is an ordinary identifier, recognised by the parser only
as the first word inside `[ ]` binders (`crates/syntax/src/parser.rs`, "`names[0].text ==
"auto"`") **[checked]**.

**`match h: e with`** (`docs/syntax.md`, "match"):

- A scrutinee that is not a plain variable is *generalised*. Wherever it appears in the
  expected type, it is replaced by the branch's pattern. The same happens in the types of
  variables in scope, which the branches see as re-bound copies.
- `match h: e with` also binds, in each branch, an equation `h: e = pattern`.
- Such a `match` is lifted into a generated definition.
- The occurrence test is syntactic: "the same term, looking through source locations and
  binder names only. No definitions are unfolded" (`crates/elab/src/matching.rs`).
- When generalising makes something else ill-typed, the error is `E-MATCH-MOTIVE`.

This is Agda's `with … in eq` (§4.3).

### 1.3 The definitions this note relies on

All quoted from `crates/elab/src/prelude.sw` (line numbers as of commit `8305858`).

Equality lemmas (lines 148 to 152):

```
theorem Eq.cong (f: a -> b) [x y: a] (p: x = y): f x = f y := J (\y' p' => f x = f y') rfl p

theorem Eq.sym [x y : a] (p : x = y) : y = x := J (\y' p' => y' = x) rfl p

theorem Eq.trans [x y z: a] (p: x = y) (q: y = z): x = z := J (\z' q' => x = z') p q
```

Logic, booleans and numbers (lines 22, 60 to 109):

```
def Not (p: Prop): Prop := p -> Void

type Nat: Type =
  | Zero
  | Succ (n: Nat)

-- `a + b` means `Nat.add a b`. It recurses on its first argument, so
-- `Succ m + n` computes to `Succ (m + n)`.
def Nat.add: Nat -> Nat -> Nat
  | Zero,   n => n
  | Succ m, n => Succ (Nat.add m n)

def Nat.sub: Nat -> Nat -> Nat
  | m,      Zero   => m
  | Zero,   Succ n => Zero
  | Succ m, Succ n => Nat.sub m n

type Bool: Type =
  | False
  | True

def Bool.ifThenElse: [a: Type] -> Bool -> (Unit -> a) -> (Unit -> a) -> a
  | True,  t, e => t Trivial
  | False, t, e => e Trivial

def Nat.leq: Nat -> Nat -> Bool
  | Zero,   n      => True
  | Succ m, Zero   => False
  | Succ m, Succ n => Nat.leq m n

def Nat.LessEq (m: Nat) (n: Nat): Prop := Nat.leq m n = True

def Nat.LessThan (m: Nat) (n: Nat): Prop := Nat.leq (Succ m) n = True
```

`a <= b` elaborates to `Nat.LessEq a b` and `a < b` to `Nat.LessThan a b`
(`crates/elab/src/numbers.rs`). Both are equations about a `Bool`, and `a < b` is
*by definition* `Succ a <= b`.

Decisions and `if` (lines 202 to 232):

```
type Decidable (p: Prop): Type =
  | Yes (proof: p)
  | No (refutation: Not p)

def Decidable.elim: [p: Prop] -> [a: Type] -> Decidable p -> (p -> a) -> (Not p -> a) -> a
  | Yes h, yes, no => yes h
  | No r,  yes, no => no r

def Bool.decTrue: (b: Bool) -> Decidable (b = True)
  | True  => Yes rfl
  | False => No Bool.falseNotTrue
```

How `if` elaborates (`check.rs`, `check_if`):

- `if c then a else b` with `c: Bool` becomes `Bool.ifThenElse c (\_ => a) (\_ => b)`.
- `if P then a else b` with a decidable proposition `P` becomes
  `Decidable.elim decision (\_ => a) (\_ => b)`. For `c < x` on `Nat`, the decision is
  `Bool.decTrue (Nat.leq (Succ c) x)`, as the motive in §2's Example 4 shows **[checked]**.

Order lemmas (lines 417 to 446):

```
theorem Nat.leTrans: (a: Nat) -> (b: Nat) -> (c: Nat) -> a <= b -> b <= c -> a <= c
  | Zero, b, c, h1, h2 => rfl
  | Succ a, Zero, c, h1, h2 => Void.exfalso (Bool.falseNotTrue h1)
  | Succ a, Succ b, Zero, h1, h2 => Void.exfalso (Bool.falseNotTrue h2)
  | Succ a, Succ b, Succ c, h1, h2 => Nat.leTrans a b c h1 h2

theorem Nat.lessTrans (m: Nat) (n: Nat) (p: Nat) (h1: m < n) (h2: n < p): m < p := Nat.leTrans (Succ m) n p h1 (Nat.lessLe n p h2)
```

The case split used throughout the proofs (line 1040):

```
theorem Bool.inspect: (b: Bool) -> (motive: Bool -> Prop) -> (b = True -> motive True) -> (b = False -> motive False) -> motive b
  | True,  m, t, f => t rfl
  | False, m, t, f => f rfl
```

### 1.4 Surface syntax used in the examples

- Declarations: `def f (n: Nat): Nat := …` and `theorem t (x: Nat): P := …`. Equations are
  written as arms after the signature (`| Zero, h, n => …`).
- Lambdas are `\x => e`, and application is juxtaposition.
- `e: T` in parentheses is a type ascription.
- `d.move t` is dot notation for `Dial.move d t`, resolved from the type of `d`.
- `++` on lists is `List.append`.
- `_` is a hole for the elaborator to fill.

## 2. The problem, with real examples

Counts in the AoC proofs at commit `8305858`, from `grep -o` **[checked]**:

| | `Eq.trans` | `Eq.cong` | `Eq.cong (\…` (hand-written motive) | `Eq.sym` | `J (` | `Bool.inspect` | `Nat.leTrans` | `Nat.le/ltCong…` |
|---|---|---|---|---|---|---|---|---|
| day 1 | 51 | 49 | 45 | 20 | 3 | 2 | 2 | 0 |
| day 2 | 54 | 43 | 35 | 16 | 0 | 6 | 11 | 3 |
| day 3 | 8 | 3 | 1 | 5 | 1 | 3 | 4 | 6 |

**Example 1, a chain of rewrites** (day 1, `stepLeftFrom`, first case). The lemma's type,
with the first case's pattern `m = Zero` substituted, is
`Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest = ((Succ highest - 1) % Succ highest + Succ n) / Succ highest`.

```
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Succ ((x + n) / Succ highest)) (Nat.modSelf (Succ highest)))
      (Eq.sym (Eq.trans (Eq.cong (\x => (x + Succ n) / Succ highest) (Nat.modSmall highest (Succ highest) (Nat.leRefl highest)))
        (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addSucc highest n)) (Nat.addDivSelf (Succ highest) n))))
```

The lemmas used are:

- `Nat.modSelf d: d % d = 0`;
- `Nat.modSmall n d h: n % d = n` (for `h: n < d`);
- `Nat.addSucc n m: n + Succ m = Succ (n + m)`;
- `Nat.addDivSelf d n: (d + n) / d = Succ (n / d)`.

The case makes three replacements and uses one division fact. Most of the text is the three
motives, the intermediate expressions are never written down, and the chain runs backwards
from the right side (`Eq.sym (Eq.trans …)`).

**Example 2, a long chain** (day 2, `writeTimesMul`, `Succ n` case). It proves
`writeTimes k b (Succ n) = b * multiplier k (Succ n)`, where `writeTimes k b (Succ n)`
computes to `writeTimes k b n * Nat.pow 10 k + b`. It has seven steps, nested seven deep:

```
  | Succ n =>
    Eq.trans (Eq.cong (\t => t * Nat.pow 10 k + b) (writeTimesMul k b n))
      (Eq.trans (Eq.cong (\t => t + b) (Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)))
        (Eq.trans (Eq.cong (\t => b * t + b) (Nat.mulComm (multiplier k n) (Nat.pow 10 k)))
          (Eq.trans (Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b)
            (Eq.trans (Eq.cong (\t => t + b * (Nat.pow 10 k * multiplier k n)) (Eq.sym (Nat.mulOne b)))
              (Eq.trans (Eq.sym (Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)))
                (Eq.cong (\t => b * t) (Eq.sym (multiplierSucc k n))))))))
```

**Example 3, an inequality chain** (day 3's `headLess`, since moved to the prelude as
`Nat.fromDigitsHeadLess`). Each `Nat.leCongLeft`, `Nat.leCongRight` and `Nat.leTrans` takes
the three numbers explicitly:

```
theorem headLess (y: Nat) (t: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
  (hd: Digits s) (h: y < t): Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons t r) :=
  Nat.leCongLeft (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons y s)) (Nat.fromDigits (Cons t r))
    (Eq.sym (fromDigitsConsLen y s r hl))
    (Nat.leCongRight (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (t * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons t r))
      (Eq.sym (Nat.fromDigitsCons t r))
      (headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r)
        (Nat.ltCongRight (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length r)) (Eq.cong (\n => Nat.pow 10 n) hl) (fromDigitsBound s hd))
        h))
```

Here `Nat.leCongLeft a b n (p: a = b) (h: a <= n): b <= n` is `J (\y q => y <= n) h p`, and
`Nat.leCongRight` is its mirror image.

**Example 4, a case split on an `if`** (day 3, `pickGe`, SW-26). `Bank.best.pick` ends with
`if c < x then pick w more x more else pick w more c after`. The motive restates the goal,
with the `if` spelled out as it elaborates (§1.3):

```
    Bool.inspect (Nat.leq (Succ c) x)
      (\b => c <= Pair.fst (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))
      (\e => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more))
      (\e => pickGe w more c after)
```

Sections 5, 6, 8 and 10 show each example rewritten.

## 3. Terms used

- **Motive.** A function that says *where* in a proposition the change happens. To turn a
  proof of `P a` into a proof of `P b` using `a = b`, you need `P` itself, the "motive".
  Today you write it: `\x => (x + n) / Succ highest`.
- **Transport** means using `J` (or `Eq.cong`) to move a proof along an equation.
- **Abstraction** is finding every occurrence of a term in an expression and replacing it
  with a variable. This is how other systems compute a motive. With goal
  `((a + 1) % d + n) % d = …` and equation `(a + 1) % d = 0`, abstracting `(a + 1) % d`
  gives the motive `\x => (x + n) % d = …`.
- **Conversion** means two terms are equal by computing, for example `0 + n` and `n`. The
  checker compares types this way. A `calc` line or a `rewrite` may therefore differ from the
  goal as long as it computes to the same thing.
- **Keyed matching** (Lean's term, §4.2) compares a subterm with the pattern only when they
  have the same head symbol and number of arguments, and then compares them by conversion.
- **Carrier type.** The type `A` that an equation `a = b` is about. `p: x = y` "at type
  `A`" means `x: A` and `y: A`.
- **Preorder chain.** A chain mixing `=` with an order such as `<=` or `<`, concluding the
  relation its steps compose to (§5.3).

## 4. How other languages do it

### 4.1 Summary table

| | `calc`-style chains | Relations in a chain | Rewrite with an inferred motive | How the motive is found | Without a known goal | Under binders |
|---|---|---|---|---|---|---|
| **Lean 4** | `calc a` / `_ = b := p` | any, through `Trans` instances; mixes `=`, `<`, `≤` | `rw [p]` (tactic), `h ▸ e` (term) | `kabstract`: keyed matching, compared by conversion | `▸` rewrites the type of `e` instead | `rw` skips subterms that mention a bound variable; `conv`'s `ext` or `simp` goes under binders |
| **Agda** | `begin a ≡⟨ p ⟩ b ∎` (library) | `≡`; `≤-Reasoning` mixes `≡`, `≤`, `<` | `rewrite p` (in a clause) | with-abstraction of the left side in the goal and argument types | n/a (always in a clause) | only occurrences visible after normalising |
| **Idris 2** | `Calc $ \|~ a ~~ b ...(p)` (library) | `=`; `Generic` adds one preorder plus `=` steps | `rewrite p in e` | normalises the goal, then replaces all occurrences of the left side | error: "Can't infer a type for rewrite" | n/a |
| **Rocq** | `transitivity b` (tactic) | relations registered as transitive | `rewrite p` (tactic) | the first match in depth-first order fixes the instance; copies of that instance are rewritten | n/a | not inside `forall` (needs `setoid_rewrite`) |
| **F\*** | `calc (rel) { a; == { p } b; … }` | any; the SMT solver checks that they combine | n/a (SMT) | n/a | n/a | n/a |
| **Dafny** | `calc { a; == { hint } b; … }` | chain-compatible operators; one `!=` with `==` | n/a (verifier) | n/a | n/a | n/a |
| **Arend** | `a ==< p >== b `qed`` (library) | `=` | `rewrite p t`, `rewriteI p t` (term) | replaces occurrences of the left side in the expected type | rewrites the type of `t` instead | not checked |

### 4.2 Lean 4

- **`calc`.** Syntax `calc a = b := pab` / `_ = c := pbc`. The first line may also be just
  `abc` followed by `_ = bce := …` lines, "useful for aligning relation symbols". "`=` can be
  replaced with any relation implementing the typeclass `Trans`" **[cited:
  [Init/NotationExtra.lean](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean),
  the `calc` docstring]**.
- **Mixing relations.** The `Trans` class's docstring says that `calc` uses it so that `a ≤ b`
  and `b < c` give `a < c`. Mixing with `=` comes free from the instances
  `Trans Eq r r` and `Trans r Eq r`, each implemented as `heq ▸ h'` **[cited:
  [Init/Prelude.lean](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean),
  `class Trans`;
  [reference, `calc`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#calc)]**.
- **`h ▸ e`**, the term-level rewrite: "Given `h : a = b` and `e : p a`, the term `h ▸ e` has
  type `p b` … The macro tries both orientations of `h`. If the context provides an expected
  type, it rewrites the expected type, else it rewrites the type of e" **[cited:
  [Lean/Parser/Term.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean),
  `subst`]**. *Theorem Proving in Lean 4* explains why it exists: inferring the motive of
  `Eq.subst` "requires an instance of higher-order unification", and `▸` "uses more effective
  heuristics" **[cited:
  [TPIL, Equality](https://lean-lang.org/theorem_proving_in_lean4/Quantifiers-and-Equality/)]**.
- **How `rw` finds the motive.** `rw [e]` with `e : a = b`:
  1. abstracts `a` in the goal with `kabstract`;
  2. builds the motive `fun _a => …`;
  3. type-checks the motive;
  4. proves the goal from the rewritten goal with `congrArg motive heq` and `Eq.mpr`.

  The source's own error text explains it: "First, it looks for all 'a' in 'e'. Second, it
  tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called
  the *motive* … if 'e' depends on specific properties of 'a', then the motive 'm' might not
  typecheck". Before abstracting, it rejects an equation whose left side has a metavariable
  at its head (`if lhs.getAppFn.isMVar then throwError "… The pattern to be substituted is a
  metavariable …"`) **[cited:
  [Lean/Meta/Tactic/Rewrite.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean)]**.
- **`kabstract` uses keyed matching.** It compares a subterm with the pattern only when they
  have the same head symbol and number of arguments, and then compares them by `isDefEq`.
  - It skips any subterm that mentions a variable bound inside the goal
    (`if e.hasLooseBVars then visitChildren ()`).
  - Metavariables "may become instantiated" by a match. For matches that are not selected,
    "the metavariable context is rolled back to prevent blocking subsequent matches which
    require different instantiations". This is the transactional matching adopted in §6.2.

  **[cited:
  [Lean/Meta/KAbstract.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean)]**

  The reference says `conv` exists for rewrites "underneath a binder that prevents tactics
  like rw from accessing the term", and for picking one part of a goal **[cited:
  [reference, `conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/)]**.
- **Pitfalls.**
  - "motive is not type correct". Mathlib's example is
    `example (h : [5] ≠ []) : List.getLast [5] h = 5 := by rw [show [5] = [5] from rfl]`:
    replacing `[5]` everywhere also changes the type of the proof `h` **[cited:
    [Mathlib KAbstractPositions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Lean/Meta/KAbstractPositions.html)]**.
    The error text in `Rewrite.lean` suggests "rewrite's 'occs' configuration option" or
    "'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these
    tactics can handle proofs and 'Decidable' instances whose types depend on the rewritten
    term …)" **[cited: Rewrite.lean]**.
  - Choosing occurrences needs `rw (occs := .pos [2])` **[cited:
    [reference, `rewrite`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rewrite)]**.
  - `←` reverses the direction (same source).
- **The general version: `@[elab_as_elim]`.** Lean elaborates a function whose result is
  `motive x₁ … xₙ` "by matching `p x₁ … xₙ` against the expected type, then replacing `xₙ`
  through `x₁` … with variables". It fails if "the expected type cannot be determined"
  **[cited:
  [Lean/Elab/App.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean),
  the `elab_as_elim` docstring]**.

### 4.3 Agda

- **`≡-Reasoning`** is a library, not built-in syntax. `x ≡⟨ x≡y ⟩ yRz` composes a step with
  the rest of the chain, `x ≡⟨⟩ xRy` is a step by computation alone, and `x ∎` ends the chain
  with reflexivity **[cited:
  [Relation.Binary.Reasoning.Syntax](https://agda.github.io/agda-stdlib/master/Relation.Binary.Reasoning.Syntax.html)]**.
- **Preorders.** `Relation.Binary.Reasoning.Base.Triple` is "equational reasoning with three
  relations: equality, strict ordering and non-strict ordering". It needs, among others,
  `<-≤-trans` and `≤-<-trans`. `Data.Nat.Properties` instantiates it as `≤-Reasoning`, used
  as `begin ∣ x - 0 ∣ ≡⟨ … ⟩ x ≤⟨ … ⟩ …` **[cited:
  [Triple.agda](https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/Reasoning/Base/Triple.agda),
  [Data/Nat/Properties.agda](https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Properties.agda)]**.
- **`rewrite`.** It "takes a term `eq` of type `lhs ≡ rhs` … and expands to a with-abstraction
  of `lhs` and `eq` followed by a match of the result of `eq` against `refl`". Its limitation:
  "you cannot do further pattern matching on the arguments *after* the rewrite" **[cited:
  [with-abstraction, Rewrite](https://agda.readthedocs.io/en/latest/language/with-abstraction.html)]**.
- **Pitfalls of with-abstraction**, from the same page:
  - "the generalisation step needs to normalise the scrutinee and the goal and argument types";
  - "this generalisation is not always type correct and may result in a (sometimes cryptic)
    type error". It "happens when you abstract over a term that appears in the type of a
    subterm of the goal".

  Porting AoC day 1 to Agda (`docs/comparisons/aoc-day01.md` §3.2), I also hit two more
  **[checked]**:
  - `rewrite` fails on an equation with an instance argument;
  - it fails when the goal has already reduced past the term.
- **`with … in eq`** names the equation between the scrutinee and the new variable **[cited:
  same page, "With-abstraction equality"]**. Stitchwort's `match h: e with` is the same idea
  (§1.2, §8).

### 4.4 Idris 2

- **`Calc`** is a library: `Calc $ |~ x ~~ y ...(p) ~~ …`. The first expression is `|~ x`,
  and each step `~~ y ...(justification)` is "ASCII art for a thought bubble" **[cited:
  [Syntax/PreorderReasoning.idr](https://github.com/idris-lang/Idris2/blob/main/libs/base/Syntax/PreorderReasoning.idr)]**.
  `Syntax.PreorderReasoning.Generic` takes one preorder `leq` and allows `=` steps (`~~`) in
  the chain. Its prerequisite is `Reflexive` for an empty chain and `Transitive` for two or
  more steps **[cited:
  [Generic.idr](https://github.com/idris-lang/Idris2/blob/main/libs/base/Syntax/PreorderReasoning/Generic.idr)]**.
  It does not mix two different orders.
- **`rewrite p in e`** "calculates the property and applies `replace`": it searches for `x`
  in the goal and "Replaces all occurrences of `x` with `y`" **[cited:
  [Idris docs, propositional equality](https://idris2.readthedocs.io/en/latest/proofs/propositional.html)]**.
  In the elaborator:
  - the goal is fully normalised (`nf`) before the search;
  - a rewrite that changes nothing is an error (`RewriteNoChange`);
  - with no known goal, the error is "Can't infer a type for rewrite" **[cited:
    [src/TTImp/Elab/Rewrite.idr](https://github.com/idris-lang/Idris2/blob/main/src/TTImp/Elab/Rewrite.idr)]**.
- **Pitfall.** In the day 1 port, `Calc` steps broke once the checker unfolded `modNatNZ`
  into its helper `mod'` (aoc-day01.md §3.3) **[checked]**.

### 4.5 Rocq (Coq)

**What the documentation says.** The current reference manual says two things that are hard
to read together **[cited:
[Rocq reference, equality](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html);
source
[equality.rst](https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/writing-proofs/equality.rst)]**:

- under the occurrences clause: "If not specified, only the first occurrence in the
  conclusion is replaced";
- in a note: "rewrite finds the first matching subterm in depth-first search order. Only
  subterms identical to that first matched subterm are rewritten".

**What it does.** Rocq 9.1.1 (from nixpkgs) behaves as the note says **[checked]**:

- `Lemma t (a b : nat) (H : a = b) : a + a = b + b.` followed by `rewrite H.` gives the goal
  `b + b = b + b`. Both copies of `a` were replaced.
- With `H : forall n, n + 0 = n`, the goal `(a + 0) + (c + 0) = a + c` becomes
  `a + (c + 0) = a + c`. The first match fixed `n := a`; the other instance, `c + 0`, was
  left alone.

So "first occurrence" means the first matched *instance*, and every identical copy of it is
rewritten.

The page also says:

- `rewrite` "won't find occurrences inside `forall` that refer to variables bound by the
  `forall`", for which there is `setoid_rewrite`;
- comma-separated rewriters "are applied sequentially";
- `transitivity b` splits a goal `t = u` (or any relation registered as transitive) into
  `t = b` and `b = u`.

### 4.6 F\*

- `calc (>) { a + a; == {} 2 * a; > { lem1 a } a; }`. Each step has a relation and a
  justification in braces. F\* checks that the step relations combine into the overall one
  ("if `a == b > c`, then `a > c`"), and "this condition is currently sent to the SMT solver"
  **[cited: [F\* wiki, Calculational proofs](https://github.com/FStarLang/FStar/wiki/Calculational-proofs)]**.
- The library keeps the list of step relations and checks `calc_chain_compatible` against
  the conclusion **[cited:
  [ulib/FStar.Calc.fsti](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Calc.fsti)]**.
  With no SMT solver, Stitchwort would need a fixed table instead (§5.3).

### 4.7 Dafny

- `calc { e0; == { hint } e1; … }`, or `calc == { … }` to give a default operator ("If that
  operator is omitted, it defaults to equality").
- Only "chain-compatible operators can be used together", and "a single occurrence of the
  intransitive operator `!=`" may appear in a chain of equalities.
- The hints are statements (lemma calls, nested `calc`s) that help the verifier prove that
  step **[cited:
  [Dafny reference §8.23](https://dafny.org/latest/DafnyRef/DafnyRef#sec-calc-statement);
  source
  [docs/DafnyRef/Statements.md](https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Statements.md)]**.

### 4.8 Arend

- `rewrite (p : a = b) t : T` "replaces occurrences of `a` in `T` with a variable `x`
  obtaining a type `T[x/a]` and returns `transportInv (\lam x => T[x/a]) p t`".
  - "If the expected type is unknown, the meta rewrites in the type of the arguments
    instead."
  - `rewrite {i_1, … i_k} p t` picks occurrences.
  - `rewrite (p_1, … p_n) t` chains.
  - `rewriteI p` is `rewrite (inv p)`.
  - `rewriteEq` matches "up to algebraic equivalences" for monoids and categories.

  **[cited:
  [arend-lib StdExtension.java](https://github.com/JetBrains/arend-lib/blob/master/meta/src/main/java/org/arend/lib/StdExtension.java)]**
- Chains are written `a ==< p >== b `qed`` with library operators **[cited:
  [arend-lib src/Paths.ard](https://github.com/JetBrains/arend-lib/blob/master/src/Paths.ard)]**.
- Arend's `rewrite` is the closest model for Stitchwort: a term, not a tactic.

(I dropped Cubical Agda: I couldn't confirm from a primary source how `rewrite` behaves with
its path type.)

### 4.9 What to take from the survey

- Every system with dependent types finds the motive the same way: abstract the equation's
  left side in a known goal, then check that the result is well typed.
- The design choices that differ between them are these:
  - how occurrences are matched: syntactically (Rocq), by keyed conversion (Lean), or after
    normalising (Idris, Agda);
  - what happens with no known goal: an error (Idris), or rewrite the argument's type
    instead (Lean's `▸`, Arend).
- The known failure modes are also the same everywhere:
  - the motive isn't well typed (a proof or instance argument mentions the term);
  - the term isn't found because the goal was normalised past it;
  - the term is under a binder.
- `calc` is a library in Agda, Idris and Arend, and built-in syntax in Lean, F\* and Dafny.
  Systems with mixed relations use a class (Lean), a module parameter (Agda) or an SMT check
  (F\*), or a fixed list (Dafny).

## 5. `calc` for Stitchwort

### 5.1 Syntax (D32, D33)

Recommended form: Lean's aligned form, one step per line.

```
  calc e0
    _ = e1  := proof1
    _ <= e2 := proof2
    _ = e3
```

- `calc e0` starts the chain. Each following line, indented more than `calc`'s line, is a
  step `_ R e := proof`.
- `R` is `=`, `<=` or `<`.
- `calc` is an expression, usable anywhere a proof is: as an argument, in a `let`, or as
  an arm's body.

**A step with no `:= proof`** (D33) means "check `rfl` against this step's proposition".
That proposition is `e(i-1) R ei`, built exactly as for a step with a proof.

- For `=`, this accepts the step when the two expressions compute to the same thing, like
  Agda's `≡⟨⟩` and Idris's `~=`. It is useful for unfolding a definition so that a later
  `rewrite` can see inside it.
- For `<=` and `<`, it accepts the step when the order proposition itself computes to
  `True = True`. That does **not** mean the endpoints are equal:
  - `calc 0` / `_ <= n` is accepted, because `Nat.leq 0 n` computes to `True` for any `n`;
  - `calc n` / `_ < n` is rejected, because `Nat.leq (Succ n) n` is stuck;
  - `calc a` / `_ <= a + n` is rejected, because `Nat.leq a (a + n)` is stuck on the
    variable `a`.

  **[checked: `0 <= n := rfl` is accepted; `n < n := rfl` and `a <= a + n := rfl` are
  rejected with `E-REFL`]**

Alternatives (D32):

- **(b)** Lean's other first line, `calc e0 = e1 := p` followed by `_ = …` lines. This
  gives two ways to write the same chain.
- **(c)** Drop the `_`: lines read `= e1 := p`. It is shorter, but a line starting with an
  operator is new to Stitchwort's layout (`docs/syntax.md` lets `|>`, `then` and `else` start
  lines, but not `=`).
- **(d)** Dafny's layout, with expressions and relations on alternate lines. It is longer, and
  the reasons sit on the relation lines.

### 5.2 What is checked

1. `e0` is inferred. Each `ei` is checked against the type of `e0`.
2. For each step, the proposition `e(i-1) R ei` is built from the elaborated expressions as
   written, not their computed forms. The step's proof, or `rfl` if there is none (§5.1), is
   checked against it.
3. The steps are combined by folding the composition table (§5.3) from left to right. The
   relation the fold ends with is the chain's conclusion `e0 R* en`.
4. Where a type is expected, `e0 R* en` is unified with it, so `e0` and `en` only need to
   *compute* to the goal's sides. Where no type is expected, the `calc` has type `e0 R* en`.
   So `calc` works in both checking and inferring positions, unlike `rewrite` (§6.4).

I checked that this conversion is enough for the examples in §10. I gave the existing proofs
type ascriptions `(p: e0 = e1)` with exactly the intermediate expressions used there, and the
checker accepted them. Two examples **[checked]**:

- the first line `Succ ((Succ highest % Succ highest + n) / Succ highest)` is accepted where
  the goal says `Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest`;
- `_ _` holes in `List.occurrencesAppend Dial.isZero _ _` are solved from the step's type.

### 5.3 Combining steps (D34)

There is no type-class mechanism, so the elaborator uses a fixed table. `R1` is the relation
proved so far, from `a` to `b` (proof `p`); `R2` is the new step, from `b` to `c` (proof `q`).

| `R1` then `R2` | Result | Term produced |
|---|---|---|
| `=`, `=` | `=` | `Eq.trans p q` |
| `=`, any `R` | `R` | `J (\w _ => w R c) q (Eq.sym p)` |
| any `R`, `=` | `R` | `J (\w _ => a R w) p q` |
| `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
| `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
| `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
| `<`, `<` | `<` | `Nat.lessTrans a b c p q` |

- The chain's relation is whatever this fold produces. For today's three relations, that
  happens to be "`<` if any step is `<`, else `<=` if any is `<=`, else `=`". The table, not
  that rule, is the definition, so an extended table needs no notion of "strength".
- A pair missing from the table (once there are more relations) is `E-CALC-MIX`.
- The `=` rows are Lean's `Trans Eq r r` and `Trans r Eq r` instances, written with `J`.
- The `Nat` rows rely on two facts from §1.3:
  - `a < b` is by definition `Nat.leq (Succ a) b = True`, the same as `Succ a <= b`;
  - `Nat.leq (Succ a) (Succ b)` computes to `Nat.leq a b`.

  So no new lemmas are needed. In the `<=`, `<` row, `p: a <= b` is accepted where
  `Succ a <= Succ b` is expected, by conversion.

I checked `<=`/`<`, `<`/`<=`, `=`/`<=` and `<=`/`=` as plain theorems **[checked]**:

```
theorem leLt (a: Nat) (b: Nat) (c: Nat) (h1: a <= b) (h2: b < c): a < c := Nat.leTrans (Succ a) (Succ b) c h1 h2
theorem ltLe (a: Nat) (b: Nat) (c: Nat) (h1: a < b) (h2: b <= c): a < c := Nat.leTrans (Succ a) b c h1 h2
theorem eqLe (a: Nat) (b: Nat) (c: Nat) (p: a = b) (h: b <= c): a <= c := J (\w q => w <= c) h (Eq.sym p)
theorem leEq (a: Nat) (b: Nat) (c: Nat) (h: a <= b) (p: b = c): a <= c := J (\w q => a <= w) h p
```

- Every produced term is re-checked by the kernel, so a wrong table entry would be rejected,
  not accepted. It would show up as a confusing error at an innocent-looking `calc`
  **[inferred from §1.2; the reviewer agreed, §12]**.
- `Int` chains need `Int.leTrans`-style lemmas first. The prelude has none: its
  `^theorem .*Trans` lines are only `Eq.trans`, `Nat.leTrans`, `Nat.lessTrans` and
  `List.permTrans` **[checked]**.
- `>`/`>=` and mixed directions are an error, as in Dafny.
- `!=` is out of scope.
- A user-extensible table (for `List.Perm`, or a user's own order) would need a way to
  register a transitivity lemma (D34).

### 5.4 Error messages

```
[E-CALC-STEP] Error: this step doesn't prove what its line says
  the line says    `(highest - j + n) / Succ highest = (Succ (highest - Succ j) + n) / Succ highest`
  the proof proves `highest - j = Succ (highest - Succ j)`
  Note: to replace part of the expression, write `rewrite Nat.subSuccRight …`

[E-CALC-STEP] Error: this step has no proof, and `rfl` doesn't prove it
  the line says `n < n`, which computes to `Nat.leq (Succ n) n = True`
  Note: a step without `:=` must hold by computation alone

[E-CALC-GOAL] Error: the chain proves `writeTimes k b n * Nat.pow 10 k + b = b * multiplier k (Succ n)`,
  but `writeTimes k b (Succ n) = b * multiplier k n` is expected
  the last line, `b * multiplier k (Succ n)`, differs from the goal's right side `b * multiplier k n`

[E-CALC-MIX] Error: `<` and `>=` go in opposite directions, so they can't be chained
```

The goal check names which end differs, so a typo in the last line doesn't look like a
broken step.

## 6. `rewrite` for Stitchwort

### 6.1 Syntax and meaning (D35)

```
rewrite p in t              -- t proves the goal with p's left side replaced by its right side
rewrite p                   -- the same as `rewrite p in rfl`
rewrite p, q in t           -- p first, then q: `rewrite p in (rewrite q in t)`
rewrite <- p in t           -- right to left: `rewrite (Eq.sym p) in t`
```

Given `p: a = b` at carrier type `A`, and an expected goal `G`:

1. Abstract `a` in `G` (§6.2), giving `G[x]` with `x` where `a` was.
2. Check that `\x _ => G[x]` is a well-typed motive, with `x: A`.
3. Check `t` against `G[b]`.
4. Produce `J (\x _ => G[x]) t (Eq.sym p)`. With `Eq.sym p: b = a`, `J` needs a base of type
   `G[b]` and gives `G[a]`, which is `G` up to conversion.

This is Lean's `rw`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's `rewrite`, in the
same direction for all four.

**Comma lists apply left to right.** `rewrite p, q in t` rewrites the goal with `p` first,
then rewrites the result with `q`, then checks `t`, as Rocq's comma-separated rewriters "are
applied sequentially" (§4.5). The nesting `rewrite p in (rewrite q in t)` says the same.

**`rewrite p` with no `in`** is `rewrite p in rfl`, against whatever proposition is expected:

- the whole of it, both sides, in any relation;
- in a `calc` step, that is the step's proposition `e(i-1) R ei`, which may be `=`, `<=` or
  `<`.

Every matching occurrence on either side is rewritten, and then `rfl` must prove the result.
In an equality step, `a` may occur on the left (it becomes `b`) or on the right (it becomes
`b`, which must then compute to the left), so `<-` is needed less often in a `calc`. It is
not unnecessary: it is the only way to replace occurrences of `b` by `a`.

For example, in §10 the step from `(Succ highest + n) / Succ highest` to
`(highest + Succ n) / Succ highest` uses `rewrite Nat.addSucc highest n`. That turns the right
side's `highest + Succ n` into `Succ (highest + n)`, which computes to the left side's
`Succ highest + n` (`Nat.add` recurses on its first argument) **[inferred; the step's
equation was checked by ascription, §5.2]**.

**Keywords** (D35, D39).

- `calc` is a reserved keyword from stage 1.
- `rewrite` is reserved in stage 2. It starts an expression, so treating it as an ordinary
  name would make `rewrite p in t` ambiguous with a call of a function named `rewrite`.
- `in` is a *contextual* keyword, recognised only where a rewrite rule list can end, as
  `auto` is recognised only at the start of a binder (§1.2). Elsewhere `in` stays an ordinary
  identifier. The cost is that a rule must put a variable named `in` in parentheses to pass it
  as an argument, as in `rewrite f (in) in t` **[inferred from the parser's `auto` precedent;
  not yet prototyped]**.
- No identifier in the repository's `.sw` files is named `calc`, `rewrite` or `in`; they
  appear only inside strings and comments **[checked: grep]**.

**Metavariables in the rule.** Implicit arguments of `p` that elaboration couldn't solve are
left as metavariables belonging to the rule. They are solved by the first occurrence that
matches, in the search order of §6.2 (outermost first, left to right), and later occurrences
must match that same instance. If the left side's
*head* is a metavariable (for example `?f x`), the rule is rejected: there is no key to
search by. Lean has the same check (`lhs.getAppFn.isMVar`, §4.2).

### 6.2 Finding occurrences (D36)

The search walks the goal term **in pre-order, outermost first, left to right**: it tries a
term before its subterms, and a function's arguments in order. **Once a candidate is
selected, the search doesn't look inside it.** The selected occurrence is replaced as a whole,
so matches never overlap. Lean's `kabstract` behaves the same way: it tries the current
expression before its children and doesn't descend into a selected match. At each subterm `c`
that doesn't mention a variable bound inside the goal (§6.3), it applies these tests in order:

1. **Key.** `c` must have the same head as `a` (the same definition, constructor or
   variable) and the same number of arguments. Otherwise, skip it and look inside.
2. **Syntax.** If `c` is the same term as `a` (`matching::same`), it is a match. This is the
   cheap common case.
3. **Carrier type.** Infer `c`'s type and compare it with `A`, the type of the equation `p`.
   If they differ, it is not a match.
4. **Conversion.** Compare `c` with `a` by conversion. This may solve the rule's own
   metavariables.

Four properties of the search:

- **Transactional, one-way matching.** Before each candidate, save the metavariable state;
  restore it if the candidate fails. Only metavariables created for the rule may be solved;
  a comparison that would need to solve a metavariable already present in the goal is a
  failure for that candidate. Lean rolls back unselected matches the same way (§4.2).
  - **The transaction covers the whole attempt,** from step 3 on. Inferring the candidate's
    type and comparing it with `A` can already constrain the rule's metavariables, so the
    state is saved before step 3, and restoring it undoes everything steps 3 and 4 did.
  - **The budget isn't rolled back.** A failed candidate still did work, and that work
    counts.
  - **Caches.** Any conversion or unification cache whose entries depend on metavariable
    assignments is either part of the transaction or invalidated when it is rolled back.

  Without the rollback, a pattern `F ?x ?x` tried against `F 1 2` could leave `?x := 1`
  behind and miss a later `F 3 3`. Once a candidate succeeds, its solutions are kept, and
  later candidates are compared with the solved pattern.
- **Why check the carrier type before conversion** (step 3).
  - The kernel's comparison is untyped (§1.1), and same head and arity don't guarantee the
    same type.
  - Comparing values of different types can solve the rule's metavariables wrongly, which
    damages implicit-argument inference before the kernel ever sees the result.
  - The proof-irrelevance proposal's option D1′ will *require* it. D1′ skips proof fields
    when comparing, which "is safe only if both values have the same type". It requires
    "every call `conv(v, w)` and `unify(v, w)` that can reach a masked comparison" to be made
    on values of the same type (`docs/proposals/proof-irrelevance.md` §1 and §7.4).
  - The rewrite matcher is a new caller that compares arbitrary subterms, so it must
    establish that invariant itself.
- **One budget, and running out is inconclusive.**
  - All comparisons in one `rewrite`, across all candidates, draw on a single search budget.
  - If a candidate that passed steps 1 to 3 exhausts it, the search stops with
    `E-REWRITE-BUDGET` (§6.3). It must not treat that candidate as "no match": that would
    make "rewrite every occurrence" depend on performance.
  - Skipping it would still be sound (rewriting fewer occurrences is a valid transport),
    but the result would be unpredictable.
  - `E-REWRITE-NOTHING` is reported only when every plausible candidate was decided and none
    matched.

- **A round-trip check after abstraction.** Once every selected occurrence is abstracted
  into a motive `M`, check that **`M a` is convertible to the original goal `G`** before
  accepting the rewrite. This applies to matches found by the syntactic fast path too.
  - **Why it's needed.** The generated `J` needs exactly this property; Lean's `rewrite`
    states it as a requirement on its motive. It normally follows from the match, because
    conversion is congruent.
  - **It isn't guaranteed once proof irrelevance lands.** The proof-irrelevance proposal's
    D1′ deliberately makes conversion non-congruent in proof-sensitive places. The
    reviewer's example:

    ```
    type Box (P: Prop): Type =
      | MkBox (h: P)

    def Box.unbox [P: Prop]: Box P -> P
      | MkBox h => h
    ```

    Under D1′, `MkBox p ≡ MkBox r` for proofs `p r: P`, because the proof field is
    masked. Suppose a rule's left side is `MkBox p`, and the goal is
    `Box.unbox (MkBox r) = r`. Then `MkBox r` matches, and the motive is
    `M x := Box.unbox x = r`. `M (MkBox r)` computes to `r = r`, the goal, but `M (MkBox p)`
    computes to `p = r`, which D1′ doesn't equate with it. The resulting `J` would be
    rejected.
  - **Failure** is reported as `E-REWRITE-MOTIVE` (§6.3), with an explanation that the match
    held only up to an ignored proof, and a hint to rewrite a larger term or use `calc`.
  - The kernel would reject such a `J` anyway, so this is about a clear message rather than
    soundness.
  - **Cost.** The check's conversion draws on the rewrite's shared budget, and running out
    there is `E-REWRITE-BUDGET`, never a silent skip.

All matching occurrences are replaced, as in Lean, Idris and Arend. Rocq rewrites every copy
of the first-matched instance (§4.5), which is the same rule once the first match has fixed
the rule's metavariables.

**Why not purely syntactic matching:**

- In `stepLeftFrom` (Example 1), the equation `Nat.modSelf (Succ highest)` is about
  `Succ highest % Succ highest`. The goal says `(Succ highest - 0) % Succ highest`. The two
  are equal by computation, not syntactically.
- The existing occurrence test for `match` is purely syntactic (§1.2). That suits `match`,
  but would make `rewrite` fail on goals like this one. The reviewer agreed and advised
  against a syntactic-only fallback (§12).

**Which form of the goal is searched:**

- In a `calc` step, the step's own elaborated sides.
- Otherwise, the expected type as the elaborator holds it (a value), read back to a term.
  Because definitions unfold lazily (§1.1), this keeps most of the user's structure. It is
  not exactly what was written: `<=` already appears as `Nat.leq a b = True` in messages
  **[checked: the `E-TYPE-MISMATCH` text in §8]**.
- The compiler can already show the type as written in one case only: "when the `rfl` is the
  whole body of a `def` or `theorem` … whose type is the `=`" (`docs/core.md`, error
  messages). It isn't available inside arms or nested terms, so `rewrite` can't rely on it.
- Searching a lightly evaluated goal avoids the Agda and Idris failure where normalising
  destroys the term being looked for (§4.3, §4.4).

### 6.3 What can go wrong, and the messages

- **Nothing found** (Idris's `RewriteNoChange`, Lean's "Did not find an occurrence"). Every
  candidate was decided and none matched.

  ```
  [E-REWRITE-NOTHING] Error: `rewrite` found no `Succ highest % Succ highest` in the goal
    goal: `((highest - j) % Succ highest + n) / Succ highest = (highest - j + n) / Succ highest`
    Note: occurrences are looked for by their outer function (`%`) and compared by computing
    Note: to replace the right side by the left, write `rewrite <- …`
  ```

- **Out of budget.** A plausible candidate couldn't be decided in the budget.

  ```
  [E-REWRITE-BUDGET] Error: `rewrite` couldn't decide whether `(x * 100) % 100` is `Succ highest % Succ highest`
    comparing them by computing ran out of budget, so the rewrite can't tell which occurrences to replace
    Note: state the step with `calc`, or rewrite with a more specific equation
  ```

- **Metavariable at the head of the rule** (§6.1):

  ```
  [E-REWRITE-RULE] Error: this equation's left side, `?f x`, starts with an unknown function
    Note: give the implicit arguments explicitly, such as `[f := …]`
  ```

- **The motive is ill typed** (Lean's "motive is not type correct", Agda's ill-typed
  with-abstraction, Stitchwort's own `E-MATCH-MOTIVE`).

  The likely cause in Stitchwort is an `auto` argument (§1.2). `x % d` carries a proof about
  `d`. Rewriting `d` either leaves that proof about the wrong number (if the proof is a
  variable `ok: d != 0`), or turns `Decidable.fromYes (decide (d != 0)) Trivial` into a term
  that no longer checks once `d` is a variable **[inferred from the definitions in §1.2; not
  yet tried, since `rewrite` doesn't exist]**.

  The day 1 notes already show that `auto` proofs found in different places are different
  terms (`docs/aoc-2025.md`, "auto proofs differ by context") **[checked]**.

  The policy is to report the error and suggest rewriting a larger term; `auto` is not re-run
  inside the motive. The reviewer agreed: replacing `d` by an arbitrary `x` gives no evidence
  that `x != 0`, so re-running the search would change the problem (§12, Q2).

  ```
  [E-REWRITE-MOTIVE] Error: replacing `d` everywhere in the goal doesn't give a valid proposition
    `x % d` also needs a proof that `d != 0`, and that proof would no longer match
    Note: rewrite a larger term that contains `d` (such as `x % d`), or state the step with `calc`
  ```

  The same code covers a failed round-trip check (§6.2), with its own explanation:

  ```
  [E-REWRITE-MOTIVE] Error: `MkBox r` matched `MkBox p` only because the proof inside is ignored
    after replacing it, the goal no longer computes to what it was
    Note: rewrite a larger term that contains it, or state the step with `calc`
  ```

- **Under a binder (D37).** Occurrences of `a` that mention a variable bound inside the goal
  can't be abstracted: `J` can't rewrite inside a function without function extensionality,
  which Stitchwort doesn't have (§1.1). They are skipped, as in Lean and Rocq.

  If nothing else matches, the message points to the pointwise lemmas the AoC proofs already
  use for this. One is `List.mapCongr (f) (g) (h: (x: a) -> f x = g x)`, with type
  `List.map f xs = List.map g xs`; there is also `List.sumByCongr`.

  Occurrences under a binder that don't mention the bound variable are rewritten normally:
  in `(x: A) -> P a x`, the free `a` can be abstracted.
- **Messages use the user's rule.** Dot notation and implicit arguments are resolved before
  the search, so internally `d.move t` is `Dial.move d t`. Messages should show the rule as
  the user wrote it, using its source span, where they can.

### 6.4 When the goal isn't known (D38)

- `rewrite … in` needs an expected type. In an inferring position (the head of an
  application, or a `let` without a type) it is an error that suggests `(rewrite p in t: T)`,
  as Idris does ("Can't infer a type for rewrite").
- Arend's and Lean's `▸` fallback, rewriting in the type of `t` instead, is a possible later
  stage.
- In practice the goal is almost always known, because proof arguments are usually checked
  against a known parameter type. In §10, `headLess` uses `(rewrite <- hl in fromDigitsBound s hd)`
  as an argument whose type is already fixed by the earlier explicit arguments.

### 6.5 Not included

- Rewriting a hypothesis in the context (Lean's `rw … at h`). Today, write
  `rewrite p in h` where `h`'s new type is expected.
- Choosing occurrences (Lean's `occs`, Arend's `{i}`): `calc` with an explicit step covers
  this.
- Matching up to algebra (Arend's `rewriteEq`): that belongs with a reflective arithmetic
  normaliser (`docs/comparisons/aoc-day01.md` §5 item 4).

## 7. What will surprise users

All of these are sound; they belong in the user documentation when the features land. The
list is the reviewer's, plus the `windowZero` case found in the SW-26 experiment.

1. **`rewrite p` in a `calc` step may rewrite the right side, or both sides,** not
   necessarily the expression on the line before. It rewrites the whole step proposition
   (§6.1).
2. **`rewrite` replaces every matching occurrence.** There is no occurrence selector in the
   first version (§6.5); use `calc` to say exactly which form you want.
3. **A rewrite can match something that isn't there textually,** because a candidate that
   *computes* to the equation's left side matches (§6.2).
4. **The first match fixes the rule's implicit arguments.** Later occurrences must be the
   same instance, as in Rocq (§4.5). Occurrences of a different instance are left alone.
5. **An obvious-looking rewrite can fail with `E-REWRITE-MOTIVE`** because an `auto` proof
   (such as the `d != 0` inside `x % d`) depends on the term being replaced (§6.3).
6. **Rewriting under binders is deliberately incomplete** (§6.3, D37).
7. **The goal searched isn't exactly the notation written.** It is the elaborated, lightly
   evaluated goal (§6.2), and messages may show `Nat.leq a b = True` for `a <= b`.
8. **`match h: e with` can change more of a branch's goal than expected.** It generalises
   every occurrence of `e`, including ones that only appear after definitions in the goal
   unfold. So branch goals may compute further than the original goal (`windowZero`, §8).
   The reviewer called this expected with-abstraction behaviour; showing the branch goal in
   messages is the remedy (§12, Q8).
9. **A proofless `_ <= e` step doesn't mean the endpoints are equal.** It means the order
   proposition computes to something `rfl` proves: `calc 0` / `_ <= n` is accepted (§5.1).
10. **`E-REWRITE-BUDGET` is about cost, not truth.** A rewrite can fail because a comparison
    was too expensive to decide, not because the occurrence was absent (§6.2).
11. **The search order decides which instance a rewrite picks.** With an implicit argument
    left open, as in `lemma: F ?n = G ?n`, the outermost, leftmost occurrence fixes `?n`.
    Given `… F 1 … F 2 …`, only the `F 1`s are rewritten. Also, a match is never searched
    inside, so an occurrence nested within a replaced one isn't rewritten separately (§6.2).
12. **If proof irrelevance (D1′) lands, a match can still be unusable.** A candidate equal
    to the left side only because a proof field is ignored fails the round-trip check as
    `E-REWRITE-MOTIVE` (§6.2).

## 8. SW-26 (`if` case splits): the existing `match h: e with` already solves it (D40)

`match h: e with` generalises `e` in the goal and binds `h: e = pattern` (§1.2). That is
exactly the motive `Bool.inspect` asks for. Its syntactic occurrence test suits this case,
because the `if` elaborates to `Decidable.elim (Bool.decTrue (Nat.leq (Succ c) x)) …`,
which contains the scrutinee as written.

**Experiment** **[checked]**:

- I copied the AoC project at commit `8305858` and replaced six `Bool.inspect` proofs with
  `match`:
  - day 3: `pickGe`, `pickLen`, `pickSub`;
  - day 2: `gaussPick`, `windowZero`, and the nested pair of splits in `window`, as one
    two-scrutinee `match hA: Nat.leq bLo s, hB: Nat.leq s bHi with`.
- I deleted `IsTrue`/`decIsTrue`.
- Built fresh from that commit, `stitchwort check` accepts the whole project.
- Changing one branch to a wrong argument is rejected:

  ```
  expected `Nat.leq c (Pair.fst (Aoc.Day03.Bank.best.pick w more c after)) = True`,
  but this has type `Nat.leq x (Pair.fst (Aoc.Day03.Bank.best.pick w more x after)) = True`
  ```

- Checking the project took 0.36 s before and after.

Before (Example 4) and after:

```
  | Succ w, Cons x more, c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after
```

Two things the experiment showed:

- **`pickSub` is the strongest case.** Its motive was a whole implication mentioning the `if`
  twice, and the hypothesis `h` was threaded through `Bool.inspect` by hand. With `match`,
  `h`'s type is generalised too, and the branches use `h` directly.
- **Generalisation can change what a branch must prove** (`windowZero`).
  - The old proof used a *constant* motive. Each branch then proved the original goal, with
    an explicit `List.filterKeep`/`List.filterSkip` step that used `h` to unfold the filter.
  - Under `match`, the condition inside `windowSum`'s filter was replaced by `True`/`False`
    as well. So the branch goals had already computed one step further, and the old branch
    terms no longer fitted.
  - The fix was to delete the now-redundant steps: the `False` branch became just
    `windowZero lo hi c (Succ s)`.
  - This is simpler, but surprising (§7, item 8).

So SW-26 needs no new elaborator feature. The work left is to:

- move the AoC proofs to `match h: e with`;
- delete `IsTrue`/`decIsTrue`;
- add a sentence to `docs/syntax.md` saying this is how to split on an `if` in a proof.

The ticket's other idea, printing `if` in goals as `if`, is separate and still worthwhile.

**Could `rewrite`'s machinery do it instead?**

- Lean's `@[elab_as_elim]` (§4.2) would let `Bool.inspect b _ t f` infer its motive by
  abstracting `b` in the goal, the same abstraction `rewrite` uses.
- I don't recommend it now: `match` already covers the cases.
- If `rewrite` lands, its keyed matcher could later replace `match`'s syntactic test.

## 9. Implementation sketch, staging and risks

### Stage 1: `calc` (small; rough guess, two to three days)

- **Lexer.** Add the keyword `calc`. Nothing else is reserved yet.
- **Parser.** Add `Expr::Calc { first, steps, span }`, where each step is
  `{ rel, rhs, proof: Option<Expr>, span }`. Layout follows `docs/syntax.md`: steps are the
  lines indented past the `calc` line, and a proof may continue on further-indented lines.
- **Elaborator** (`check.rs`, plus a new module):
  - infer `e0`, and check each `ei` at its type;
  - build each step's proposition `e(i-1) R ei` with the existing comparison code
    (`numbers.rs`);
  - check each step's proof against it, or check `rfl` against it when there is no proof;
  - fold the steps with the §5.3 table;
  - unify the result with the expected type, if there is one.
- **Kernel.** No change. The output is ordinary `Eq.trans`/`J`/`Nat.leTrans` terms, which the
  kernel re-checks.
- **Tests.**
  - Accept: the §10 `calc` texts, a `<`/`<=` mix, a chain in an inferring position, and
    `calc 0` / `_ <= n` without a proof.
  - Reject: `calc n` / `_ < n` without a proof, and each `E-CALC-*` message, as snapshots.

### Stage 2: `rewrite` (medium; rough guess, four to six days)

- **Lexer and parser.**
  - Add the keyword `rewrite`, the `<-` token, and the contextual `in` (§6.1).
  - Add `Expr::Rewrite { rules: Vec<(reverse, Expr)>, body: Option<Expr>, span }`.
- **Elaborator, check mode only.**
  - Infer each rule, keep its unsolved implicit arguments as rule metavariables, and require
    an `Eq` type.
  - Reject a left side with a metavariable at its head.
  - Pick the term to search (§6.2), and run the search: key, syntax, carrier type, then
    budgeted conversion, transactional per candidate.
  - Abstract the matches, check the motive, check that `M a` converts to the original goal
    (the round trip, §6.2), check the body against the rewritten goal, and produce `J`.
  - The search order is pre-order, outermost first and left to right, and it never looks
    inside a selected match.
  - Rules in a comma list are applied left to right.
- **Reuse.** `lift::replace_with` with a hook is already the "replace matching subterms by a
  variable" walk that `let` refolding and `match` generalisation use. The new parts are the
  typed, keyed, transactional comparison and the shared budget.
- **Metrics.** Record, per `rewrite` and in total for a file:
  - candidate subterms visited, and how many passed the key test;
  - conversion calls;
  - evaluation steps used;
  - conversion-cache hits.

  These show whether keyed conversion is expensive on real programs. Report them under a
  debug flag, or in the benchmark harness (`crates/bench`).
- **Tests.**
  - The §10 rewrite-only texts.
  - Each failure in §6.3: nothing found; budget exhausted (an expensive `% 100` candidate);
    a metavariable-headed rule; the `x % d` `auto` case; an occurrence under a binder.
  - The `F ?x ?x` rollback case from §6.2.
  - A candidate of the wrong carrier type that would otherwise convert.
  - **Order:** `lemma: F ?n = G ?n` against a goal with `F 1` before `F 2`. `?n` becomes 1,
    and only the `F 1`s are rewritten.
  - **Nesting:** a goal where both an outer term and a term inside it match. The outer one is
    replaced, and the inner one isn't searched separately.
  - **Rollback of step 3:** a candidate whose carrier-type check constrains a rule
    metavariable and then fails conversion leaves nothing behind.
  - **Round trip:** a test that fails the `M a ≡ G` check. The Box example needs D1′; until
    D1′ exists, the check is exercised by a unit test that calls it on a deliberately
    mismatched motive.

### Stage 3 (later, if wanted)

- Rewrite in the body's own type when no goal is known (Arend's and `▸`'s behaviour).
- Choosing occurrences.
- Keyed matching for `match` generalisation.
- `Int` order lemmas, so `calc` works on `Int`.

### Risks

- **Which form of the goal is searched.** If it is too evaluated, the term isn't found (the
  Agda and Idris failures). If it is too literal, an equal-by-computation term isn't found.
  Keyed matching is the mitigation, and the stage 2 tests are the check.
- **`auto` arguments.** These are the most likely cause of ill-typed motives (§6.3). Two
  occurrences of `x % d` with different `ok` proofs may also fail to match, since proofs
  aren't irrelevant (§1.1). The [proof-irrelevance proposal](proof-irrelevance.md) would
  let such occurrences match, provided the matcher keeps its same-type invariant (§6.2). It
  would not remove every problem, because its comparison isn't congruent in proof-sensitive
  places. The round-trip check (§6.2) turns those cases into a clear `E-REWRITE-MOTIVE`.
- **Cost.** Keyed conversion runs a comparison at each plausible candidate. The shared budget
  bounds it, `E-REWRITE-BUDGET` makes exhaustion visible, and the stage 2 metrics show
  whether it matters.
- **Messages.** The motive is invisible to the user, so errors must show the goal and what
  was looked for (§6.3), not the motive's raw term.
- **Over-use.** As with Agda, a proof that is a long `rewrite a, b, c, d in rfl` is short but
  hides why it works. The house rule in D41 is the counterweight.
- **DESIGN.md is out of date.** §6 lists `rewrite` among the existing "library functions";
  there is no `rewrite` in the prelude today **[checked: grep]** (D42).

## 10. Effect on proof size

I rewrote five real lemmas by hand. Sizes are characters with runs of spaces and newlines
squeezed to one, comments and blank lines removed, as in aoc-day01.md.

- Before: the files at commit `a522d9c`. These lemmas are unchanged since, except that
  `headLess` moved to the prelude with prefixed names.
- After: the texts below. They are not runnable today, but every `calc` line's intermediate
  expression was checked by the ascription method of §5.2 **[checked]**.
- The rewrite-only versions also need keyed matching (§6.2) **[inferred]**.

| Lemma | Now | With `calc` | With `rewrite` only |
|---|---|---|---|
| `stepLeftFrom` (day 1, both cases) | 1,025 | 1,228 (+20%) | 709 (−31%) |
| `zerosPassedSplit` (day 1) | 760 | 783 (+3%) | 415 (−45%) |
| `writeTimesMul` (day 2) | 664 | 792 (+19%) | not written |
| `headLess` (day 3, `<=` chain) | 770 | 550 (−29%) | not written |
| `pickGe` (day 3, SW-26) | arm body of 4 lines | `match`: 3 lines, no motive | not applicable |

**[checked: measured with `tr -s ' \n' ' ' | wc -c`]**

`calc` versions:

```
  | Zero,   h, n =>
    calc Succ ((Succ highest % Succ highest + n) / Succ highest)
      _ = Succ (n / Succ highest)                    := rewrite Nat.modSelf (Succ highest)
      _ = (Succ highest + n) / Succ highest          := Eq.sym (Nat.addDivSelf (Succ highest) n)
      _ = (highest + Succ n) / Succ highest          := rewrite Nat.addSucc highest n
      _ = (highest % Succ highest + Succ n) / Succ highest
                                                     := rewrite Nat.modSmall highest (Succ highest) (Nat.leRefl highest)
  | Succ j, h, n =>
    calc ((highest - j) % Succ highest + n) / Succ highest
      _ = (highest - j + n) / Succ highest           := rewrite Nat.modSmall (highest - j) (Succ highest) (Nat.subLe highest j)
      _ = (Succ (highest - Succ j) + n) / Succ highest
                                                     := rewrite Nat.subSuccRight j highest (Nat.leTrans (Succ j) (Succ (Succ j)) highest (Nat.leSucc (Succ j)) h)
      _ = (highest - Succ j + Succ n) / Succ highest := rewrite Nat.addSucc (highest - Succ j) n
      _ = ((highest - Succ j) % Succ highest + Succ n) / Succ highest
                                                     := rewrite Nat.modSmall (highest - Succ j) (Succ highest) (Nat.subLe highest (Succ j))
```

```
  | Succ n =>
    calc writeTimes k b n * Nat.pow 10 k + b
      _ = b * multiplier k n * Nat.pow 10 k + b         := rewrite writeTimesMul k b n
      _ = b * (multiplier k n * Nat.pow 10 k) + b       := rewrite Nat.mulAssoc b (multiplier k n) (Nat.pow 10 k)
      _ = b * (Nat.pow 10 k * multiplier k n) + b       := rewrite Nat.mulComm (multiplier k n) (Nat.pow 10 k)
      _ = b + b * (Nat.pow 10 k * multiplier k n)       := Nat.addComm (b * (Nat.pow 10 k * multiplier k n)) b
      _ = b * 1 + b * (Nat.pow 10 k * multiplier k n)   := rewrite Nat.mulOne b
      _ = b * (1 + Nat.pow 10 k * multiplier k n)       := rewrite Nat.mulDistribLeft b 1 (Nat.pow 10 k * multiplier k n)
      _ = b * multiplier k (Succ n)                     := rewrite multiplierSucc k n
```

```
theorem headLess (y: Nat) (t: Nat) (s: List Nat) (r: List Nat) (hl: List.length s = List.length r)
  (hd: Digits s) (h: y < t): Nat.fromDigits (Cons y s) <= Nat.fromDigits (Cons t r) :=
  calc Nat.fromDigits (Cons y s)
    _ = y * Nat.pow 10 (List.length r) + Nat.fromDigits s  := fromDigitsConsLen y s r hl
    _ <= t * Nat.pow 10 (List.length r) + Nat.fromDigits r :=
      headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r) (rewrite <- hl in fromDigitsBound s hd) h
    _ = Nat.fromDigits (Cons t r)                          := Eq.sym (Nat.fromDigitsCons t r)
```

```
theorem zerosPassedSplit (d: Dial highest) (t: Turn) (ts: List Turn):
    zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
      = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts) :=
  calc List.occurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move d (t.clicks ++ List.concatMap Turn.clicks ts)))
    _ = zerosAfter d t.clicks + zerosAfter (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts)
        := rewrite List.scanLeftAppend Dial.move d t.clicks (List.concatMap Turn.clicks ts) in List.occurrencesAppend Dial.isZero _ _
    _ = d.zerosDuring t + zerosAfter (List.foldLeft Dial.move d t.clicks) (List.concatMap Turn.clicks ts) := rewrite turnCount d t
    _ = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts)                          := rewrite turnAt d t
```

The lemmas used:

- `zerosAfter d ts` is defined as `List.occurrences Dial.isZero (List.drop 1 (List.scanLeft Dial.move d ts))`;
- `turnCount d t: zerosAfter d t.clicks = d.zerosDuring t`;
- `turnAt d t: List.foldLeft Dial.move d t.clicks = d.move t`;
- `List.scanLeftAppend` and `List.occurrencesAppend` split `scanLeft` and `occurrences` over
  `++`.

`rewrite`-only versions:

```
  | Zero,   h, n =>
    rewrite Nat.modSelf (Succ highest), Nat.modSmall highest (Succ highest) (Nat.leRefl highest), Nat.addSucc highest n
      in Eq.sym (Nat.addDivSelf (Succ highest) n)
  | Succ j, h, n =>
    rewrite Nat.modSmall (highest - j) (Succ highest) (Nat.subLe highest j),
        Nat.modSmall (highest - Succ j) (Succ highest) (Nat.subLe highest (Succ j)),
        Nat.subSuccRight j highest (Nat.leTrans (Succ j) (Succ (Succ j)) highest (Nat.leSucc (Succ j)) h),
        Nat.addSucc (highest - Succ j) n
      in rfl
```

```
theorem zerosPassedSplit (d: Dial highest) (t: Turn) (ts: List Turn):
    zerosAfter d (t.clicks ++ List.concatMap Turn.clicks ts)
      = d.zerosDuring t + zerosAfter (d.move t) (List.concatMap Turn.clicks ts) :=
  rewrite <- turnCount d t, <- turnAt d t
    in Eq.trans (Eq.cong (List.occurrences Dial.isZero) (List.scanLeftAppend Dial.move d t.clicks (List.concatMap Turn.clicks ts)))
      (List.occurrencesAppend Dial.isZero _ _)
```

What this shows **[inferred]**:

- **`rewrite` is where the size goes.** It removes the motives, which are most of the
  text. On these samples it saves a third to a half, in line with Agda, whose `rewrite` got
  the day 1 proof to 8,100 characters against Stitchwort's 11,500 (aoc-day01.md §1).
  Extrapolating, days 1 and 2 would shrink by roughly 30 to 40% if written mainly with
  `rewrite`. This is an estimate from five lemmas, not a measurement.
- **`calc` buys readability, not size.** Every intermediate expression is visible and checked,
  the chain reads top to bottom (no `Eq.sym (Eq.trans …)` running backwards), and a wrong
  step is reported on its own line. For `=` chains it costs 3 to 20% more characters. For
  `<=` chains it is shorter, because it fills in `Nat.leTrans`'s three explicit arguments.
- **Used together**, `calc` with `rewrite` steps makes long chains readable and short chains
  short (D41).

## 11. Questions for the reviewer (draft 2)

These were the open questions in draft 2. The reviewer's answers are in §12.

1. Keyed matching versus conversion cost: is it affordable, what should running out of budget
   mean, and would syntactic matching be enough?
2. `auto` proofs inside motives: report an error, or re-run `auto` in the motive?
3. Under binders: is skipping occurrences that mention a bound variable right without
   function extensionality?
4. Is the mixed-relation table sound, and is "strongest relation wins" the right conclusion?
5. Implicit arguments and dot notation in rules.
6. Should `rewrite p` in a `calc` step search only the left side?
7. Syntax: the `calc` layout, reserving `in`, the order of `rewrite p, q`.
8. Is the `windowZero` generalisation surprise expected?
9. Anything unsound, or anything that will surprise users?

## 12. Review answers

The external review of draft 2 answered as follows. The changes they led to are listed in
"Changes since draft 2".

1. **Cost of keyed matching.** Keep keyed conversion matching, with no syntactic-only
   fallback: the motivating examples need conversion. Compare syntactically first, convert
   only same-key, same-arity, same-type candidates, and charge everything to one budget.
   Running out is inconclusive and must be reported. Collect metrics in stage 2. (Adopted:
   §6.2, §6.3, §9.)
2. **`auto` proofs in motives.** Fail clearly and suggest rewriting a larger term; don't
   re-run `auto` in the motive. A proof of `d != 0` really depends on `d`, and finding
   another would change the problem. (Adopted: §6.3.)
3. **Under binders.** Skip occurrences that depend on bound variables. There is no cheap
   general improvement without congruence or extensionality reasoning; `List.mapCongr`-style
   lemmas are the right escape hatch. Free occurrences under a binder can still be
   rewritten. (Adopted: §6.3.)
4. **Mixed-relation table.** Sound: a wrong term is rejected by the kernel, and the
   combinations are logically correct. Define the conclusion by folding the table rather
   than by "strongest wins". (Adopted: §5.2, §5.3.)
5. **Implicit arguments and dot notation.** "The first match fixes the rule's implicit
   arguments" is right, provided matching is transactional, only rule-side metavariables are
   solved, the carrier type is checked first, and metavariable-headed left sides are
   rejected. Dot notation resolved before matching is right; messages should keep the
   user's syntax. (Adopted: §6.1, §6.2, §6.3.)
6. **`rewrite p` in a `calc` step.** Don't restrict it to the left side. That would make the
   same syntax mean different things in different places. Define it as `rewrite p in rfl`
   against the whole step proposition, and document that `<-` is less common but not
   unnecessary. (Adopted: §6.1, §7.)
7. **Syntax.** The aligned `calc` form is the best of the options. Make `in` contextual if the
   parser allows. Document that comma lists apply left to right. (Adopted: §6.1.)
8. **`windowZero`.** Expected with-abstraction behaviour, not a sign that the search is
   wrong. Restricting it arbitrarily could make branch contexts inconsistent. Document it,
   and show branch goals well. (Adopted: §7, item 8.)
9. **Soundness and surprises.** No kernel-unsound feature found. The surprises are listed in
   §7.

The review also said current Rocq replaces only the first occurrence by default. Running
Rocq 9.1.1 showed otherwise (§4.5); the survey keeps draft 2's description, now checked.

**The second review (of draft 3)** re-answered the same questions. A summary:

1. **Keyed matching and its cost.** Still agreed, with the single budget and
   `E-REWRITE-BUDGET`. Add the round-trip `M a ≡ G` check, charged to the budget, never
   skipped silently. (Adopted: §6.2.)
2. **`auto` in motives.** Still don't re-run `auto`. "Rewrite a larger term" is the right
   escape hatch.
3. **Under binders.** Still agreed.
4. **Mixed relations.** Resolved and built.
5. **Implicit arguments and dot notation.** The first-match policy is fine once the search
   order is specified, and the transaction must cover the carrier-type check too. (Adopted:
   §6.2.)
6. **`rewrite p` in `calc`.** Still agreed.
7. **Syntax.** Contextual `in` is good. Say "parentheses", not "brackets". (Adopted: §6.1.)
8. **`windowZero`.** Unchanged.
9. **Surprises.** No new unsoundness. Two new surprises: the search order picks the
   instance, and D1′ can make a match unusable. (Adopted: §7, items 11 and 12.)

Its verdict: implement `rewrite` once the round-trip check and the search order are added.
Draft 4 adds both.

## 13. Decisions

Each decision has a stable ID. All were accepted by Matt on 20 October 2026.

| ID | Decision | Recommendation | Review of draft 2 |
|---|---|---|---|
| D32 | `calc` syntax (§5.1) | Only the aligned form, `calc e0` then `_ R e := proof` lines. | Agree |
| D33 | Steps without a proof (§5.1) | Allowed; a step with no proof means "check `rfl` against `e(i-1) R ei`". | Agree with changes (made: was "the endpoints are convertible") |
| D34 | Relations in a chain (§5.3) | `=`, `<=` and `<` on `Nat`, mixed freely, from a fixed composition table. The chain's relation is the fold of the table. `Int` once its transitivity lemmas exist. A user-extensible table later, if ever. | Agree with changes (made: fold, not "strongest wins") |
| D35 | `rewrite` surface (§6.1) | `rewrite p in t`, `rewrite p` (meaning `in rfl` against the whole proposition), `rewrite p, q in t` applied left to right, ASCII `<-` for right to left. `in` contextual. | Agree with changes (made: contextual `in`, left-to-right stated) |
| D36 | Matching occurrences (§6.2) | Keyed matching: key, syntax, carrier type, then conversion. Transactional, one-way matching of rule metavariables; reject a metavariable-headed left side. One shared budget, with exhaustion reported as `E-REWRITE-BUDGET`. Rewrite all occurrences. Search pre-order, outermost first, left to right, never inside a selected match; the transaction covers the carrier-type check; after abstraction, check `M a ≡ G` (draft 4). | Draft 2: agree with changes (made: all four). Draft 3: agree with changes (made: round trip, order, transaction scope) |
| D37 | Under binders (§6.3) | Skip occurrences that mention a bound variable, and point to `List.mapCongr`-style lemmas. No function extensionality. | Agree |
| D38 | Goal not known (§6.4) | An error with a type-ascription hint for now. Arend's "rewrite the argument's type instead" possibly in stage 3. | Agree |
| D39 | Staging (§9) | `calc` first (small, no new inference, useful at once for `<=` chains), then `rewrite`. Reserve only `calc` in stage 1. | Agree (keyword timing adopted) |
| D40 | SW-26 (§8) | Close it without new machinery: move the AoC `Bool.inspect` proofs to `match h: e with` (done for six in the experiment), delete `IsTrue`/`decIsTrue`, document the idiom. "Print `if` in goals as `if`" becomes its own ticket. | Agree |
| D41 | House style once both exist (§10) | `rewrite` for one to three replacements; `calc` when the intermediate forms help the reader or the chain mixes relations. Then convert the AoC proofs. | Agree |
| D42 | DESIGN.md §6 (§9) | Correct the claim that `rewrite` is a library function, and link this note. | Agree |

## As built (stage 2, SW-153)

`rewrite` is in `crates/elab/src/rewrite.rs`. User documentation is in `docs/syntax.md`
("`rewrite`"). The sections above are the design; this records how the build differs, and what
it measured.

**Decided after the build (Matt, 20 October 2026).** D70: accepted that inside a `calc` step
`rewrite` searches the step as it computes, with messages showing it as written (deviation 1
below). D71: the bulk conversion of the AoC proofs to `rewrite` and `calc` (D41) and SW-26
waits until the proof-checking speed work (SW-154) lands.

**Built as designed.**

- **Syntax (§6.1).** `rewrite` is a keyword. `rewrite p in t`, `rewrite p` (`in rfl`),
  `rewrite p, q in t` (left to right) and `<-`. `in` is contextual: it ends a rule only
  outside brackets and inside a rule, so `(in)` and a variable named `in` work. `<-` is not a
  token of its own (`a<-1` stays a comparison and a negative): the parser reads `<` followed
  directly by `-` after `rewrite` or a comma.
- **Check mode only (§6.4).** Inferring position is `E-REWRITE-NO-GOAL`, with the ascription hint.
- **Search (§6.2).** Pre-order, outermost first, left to right, never inside a selected
  match, built on `lift::replace_with` with a hook. Tests per candidate: key (head and
  arity), mentions a bound variable (skipped, D37), syntax, carrier type, budgeted conversion.
  The transaction (`undo::Snapshot`) starts before the carrier-type check and is undone on any
  failure. Only metavariables made while elaborating the rule may be solved: after a
  successful comparison, any solved metavariable older than the rule's fails the candidate and
  is rolled back. The budget is not refunded. After a match the rule's left side is read back
  so later copies match by syntax.
- **Budget (§6.2).** One budget per `rewrite` (all its rules), `1_000_000` evaluation steps
  (`Elaborator::rewrite_budget` overrides it, for tests). Running out is `E-REWRITE-BUDGET`
  and doesn't stop the declaration. It is `Budget::limited` in `crates/core/src/budget.rs`: a
  nested limit that, when it is the thing that ran out, un-latches the operation's exhaustion.
- **After abstraction.** The motive body is kernel-checked in the goal's context with
  `x: carrier` and `_: rhs = x` (`E-REWRITE-MOTIVE`), then `M a ≡ G` is checked
  (`round_trip`, charged to the budget; `E-REWRITE-MOTIVE` with its own text; a unit test calls it
  on a deliberately mismatched motive, as §9 says). Then the `J` is `J M t (Eq.sym p)`
  (`p` itself for `<-`). The kernel's rules are unchanged.
- **Errors.** `E-REWRITE-NOTHING`, `E-REWRITE-BUDGET`, `E-REWRITE-RULE` (unknown head, or not an
  equation), `E-REWRITE-MOTIVE`, and one the note didn't name, `E-REWRITE-NO-GOAL`.
- **Metrics (§9).** `STITCHWORT_REWRITE_METRICS=1` prints one line per `rewrite`: subterms
  visited, keyed, skipped under a binder, syntactic matches, comparisons by conversion,
  occurrences replaced, evaluation steps used by the comparisons. There is no conversion cache,
  so `cache_hits` is always 0 (§6.2's "caches" point has nothing to attach to today).

**Differences from the text.**

1. **The goal searched is always the goal as it computes, also in a `calc` step (§6.2).**
   The note said a `calc` step searches its own elaborated sides. That was built first and
   failed on the §10 chain's last line: the step's proposition (as written) keeps
   `multiplier k (Succ n)` folded, but the rule `multiplierSucc k n`'s left side is read from
   an evaluated type, where `multiplier` has unfolded to its `List.foldLeft`, so the key never
   matched. Evaluated against evaluated is consistent: with it, every line of §10's
   `writeTimesMul` chain passes. The step as written is used only in messages, with the
   computed goal underneath ("searched as it computes").
2. **Some definitions unfold before the search sees them.** `x % d` is `Nat.mod x d`, a
   definition with no case tree, so it unfolds at once to `x - Nat.mul (Nat.divFuel x x d) d`.
   Two consequences for §6.3. A goal with concrete arguments is already a number
   (`fib 27` is `196418`), so a rule about `fib 26` finds nothing. And the `auto` proof of
   `x % d` is gone by the time the motive is built, because `Nat.mod`'s body doesn't use it: the
   note's `x % d` example is accepted. `E-REWRITE-MOTIVE` shows with a definition that keeps the
   proof (`examples/reject/rewrite-motive-auto.sw`: an opaque `g` taking `[auto ok: d != 0]`).
3. **Pending `auto` obligations are proved early inside a rewrite.** Such an argument is a
   metavariable in the goal until the declaration ends, and abstracting `d` turns `?ok x d` into
   `?ok x z`, whose later solution ignores `z`: the kernel would reject the result with no
   hint. Before searching, `rewrite` proves the obligations that appear in its goal
   (`Elaborator::prove_now`, in a transaction; one that can't be proved yet is left alone), so the
   proof is a term when the motive is checked.
4. **The carrier-type test is weaker than §6.2 describes, for terms the kernel can't type.**
   The kernel infers the type of a definition or variable application, but a constructor or a
   function is only *checked* against a type, and `\x => x` checks at any `a -> a`. For those,
   the candidate is checked against the carrier if it has no unsolved metavariable, and
   otherwise (or if the candidate has one) the type test is skipped and conversion decides. The
   typed test exists mainly for proof irrelevance (D1′), which isn't built; today it can only
   reject a candidate whose head is a definition or a variable.
5. **A match by syntax skips the type test, so it can be of the wrong type.** That is §6.2's
   order, and the motive check catches it: two copies of `\x => x`, one at `Bool -> Bool` and
   one at `Nat -> Nat`, are the same term, and a rule about the `Nat` one meets the `Bool` one
   first, ending in `E-REWRITE-MOTIVE` rather than rewriting the right one. The §7 list gains this
   as an item in `docs/syntax.md`.
6. **Kernel context for candidates.** The kernel never meets metavariables, and compares a
   solved one's head as it is, so the types and values of the context, the carrier and the
   right side are read back with solved metavariables replaced before the kernel sees them
   (`kernel_context`). `kernel::Ctx::with_variables` and a public `bind` are the only
   additions to `crates/core/src/check.rs`.
7. **`rewrite p` with a failing `rfl`** adds a note with the goal after the rewrite.

**Tests.**

- `examples/accept/rewrite.sw`: every form, order, nesting, the `F ?x ?x` rollback
  (`rolledBack`), the step-3 rollback (`rolledBackType`), under a binder, in a `calc` step,
  `in` as a name and as an argument, and the §10 `stepLeftFrom` case.
- `examples/reject/rewrite-*.sw` with snapshots: nothing found (both directions), unknown head,
  not an equation, ill-typed motive (`auto`), no goal, under a binder, first instance fixes the
  arguments, body mismatch.
- `crates/driver/tests/rewrite.rs`: budget exhaustion (with a small budget), that one
  `rewrite`'s budget isn't another's, keyword. Unit tests in `rewrite.rs`: the round trip,
  carrier types, keys, bound variables. In `budget.rs`: `limited`. In the parser: rules, `<-`, `in`.
- Not tested by an example: the Box case of §6.2 (needs D1′), and a real expensive `% 100`
  candidate (no goal keeps one: see difference 2); the small budget stands in for it.

**Measured on real programs** (`aoc/`, after converting three proofs: `zerosPassedSplit` and
`stepLeftFrom` to `rewrite`, `writeTimesMul` to a `calc` of `rewrite` steps):

| | |
|---|---|
| `rewrite`s / rules | 9 / 15 |
| subterms visited | 947 |
| with the right head and arity | 57 |
| matched by syntax alone | 22 |
| comparisons by type and conversion | 30 |
| evaluation steps in them (all) | 6,570 |
| most steps in one `rewrite` | 1,482, against a budget of 1,000,000 |
| project check time | 0.58 s, as before (0.53 to 0.6 s) |

So keyed conversion costs nothing noticeable on these. The cost to watch is the number of
keyed candidates when a rule's head is common (`Nat.sub`, `Nat.add` after `%` unfolds): the
worst `rewrite` had 23 keyed candidates and 15 comparisons.

**Left for later.**

- Rewriting in the body's own type when no goal is known (§6.4, stage 3), and choosing occurrences.
- Showing a goal in messages as it was written. It is only done for a `calc` step's line and a
  definition's own type; elsewhere `x % d` shows as `Nat.mod x d`, and the searched form as
  `x - Nat.mul …`.
- A rule stated with `x % d` whose left side differs after unfolding in a way the evaluator
  doesn't make equal is a "found nothing" with the computed goal shown. Whether to search a
  second, written form is a design question, not a bug.

## Sources

- Lean 4:
  - [*Theorem Proving in Lean 4*, Quantifiers and Equality](https://lean-lang.org/theorem_proving_in_lean4/Quantifiers-and-Equality/)
  - Lean reference, [Tactic Reference](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) (`rw`, `rewrite`, `calc`, `Trans`) and [`conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/)
  - Lean source:
    - [Init/NotationExtra.lean](https://github.com/leanprover/lean4/blob/master/src/Init/NotationExtra.lean) (`calc`)
    - [Init/Prelude.lean](https://github.com/leanprover/lean4/blob/master/src/Init/Prelude.lean) (`Trans`)
    - [Lean/Parser/Term.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Parser/Term.lean) (`▸`)
    - [Lean/Meta/Tactic/Rewrite.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean)
    - [Lean/Meta/KAbstract.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean)
    - [Lean/Elab/App.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean) (`elab_as_elim`)
  - [Mathlib.Lean.Meta.KAbstractPositions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Lean/Meta/KAbstractPositions.html)
- Agda:
  - [With-abstraction](https://agda.readthedocs.io/en/latest/language/with-abstraction.html) (Rewrite; Ill-typed with-abstractions; With-abstraction equality)
  - stdlib [Relation.Binary.Reasoning.Syntax](https://agda.github.io/agda-stdlib/master/Relation.Binary.Reasoning.Syntax.html), [Reasoning/Base/Triple.agda](https://github.com/agda/agda-stdlib/blob/master/src/Relation/Binary/Reasoning/Base/Triple.agda), [Data/Nat/Properties.agda](https://github.com/agda/agda-stdlib/blob/master/src/Data/Nat/Properties.agda)
- Idris 2:
  - [Propositional equality](https://idris2.readthedocs.io/en/latest/proofs/propositional.html)
  - [Syntax/PreorderReasoning.idr](https://github.com/idris-lang/Idris2/blob/main/libs/base/Syntax/PreorderReasoning.idr), [Syntax/PreorderReasoning/Generic.idr](https://github.com/idris-lang/Idris2/blob/main/libs/base/Syntax/PreorderReasoning/Generic.idr)
  - [src/TTImp/Elab/Rewrite.idr](https://github.com/idris-lang/Idris2/blob/main/src/TTImp/Elab/Rewrite.idr)
- Rocq:
  - [Reasoning with equalities](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html) (`rewrite`, `transitivity`) and its source [equality.rst](https://github.com/rocq-prover/rocq/blob/master/doc/sphinx/proofs/writing-proofs/equality.rst)
  - Rocq 9.1.1 from nixpkgs, for the occurrence behaviour in §4.5
- F\*: [wiki, Calculational proofs](https://github.com/FStarLang/FStar/wiki/Calculational-proofs); [ulib/FStar.Calc.fsti](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Calc.fsti)
- Dafny: [Reference manual §8.23, Calc Statement](https://dafny.org/latest/DafnyRef/DafnyRef#sec-calc-statement) ([source](https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Statements.md))
- Arend: [arend-lib StdExtension.java](https://github.com/JetBrains/arend-lib/blob/master/meta/src/main/java/org/arend/lib/StdExtension.java) (`rewrite`, `rewriteI`, `rewriteEq`); [src/Paths.ard](https://github.com/JetBrains/arend-lib/blob/master/src/Paths.ard)
- Stitchwort (repository paths, for the owner; the reviewer doesn't need them):
  - `aoc/src/day01/day01.sw`, `aoc/src/day02/day02.sw`, `aoc/src/day03/day03.sw`
  - `docs/comparisons/aoc-day01.md`, `docs/aoc-2025.md`
  - `docs/core.md`, `docs/syntax.md`, `DESIGN.md` §6, `docs/proposals/proof-irrelevance.md`
  - `crates/core/src/value.rs`, `crates/elab/src/{check.rs, matching.rs, numbers.rs, prelude.sw}`,
    `crates/syntax/src/parser.rs`
  - experiments in a scratch directory, not committed: the `match` versions of six proofs,
    the ascription checks of every `calc` line in §10, and the proofless-step probes in §5.1

# `calc` chains and a `rewrite` term (SW-99), draft 2

**Date:** 19 October 2026. **Ticket:** SW-99 (related: SW-26). **Decisions:** D32 to D42.
**Status:** proposed, awaiting external review. Nothing is implemented.

**Changes from draft 1:**

- §1 is new: background for a reader without the repository.
- The decisions now carry stable IDs (D32 to D42).
- §10 is new: questions for the reviewer.
- The SW-26 experiment was re-run on the restructured AoC project, and extended to two more
  proofs (§7).

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
2. **`rewrite p in t`** (and `rewrite p` alone, which closes the step by computation). The
   motive is found by looking for the left side of `p` in the goal and replacing it. This is
   the mechanism of Lean's `rw`/`▸`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's
   `rewrite`.

Measured on five real lemmas (§8):

- `rewrite` alone makes them 31 to 45% shorter.
- `calc` makes them about as long as now, and sometimes longer. Every intermediate
  expression is written out and checked, so a reader can follow the proof line by line.
- `calc` is 29% shorter on the `<=` chain, because it fills in `Nat.leTrans`'s arguments.

**SW-26 needs neither.** The existing `match h: e with` already does Agda-style
*with-abstraction*. I replaced six of the 11 `Bool.inspect` proofs with it, and they all
check **[checked]**:

- day 3: `pickGe`, `pickLen`, `pickSub`;
- day 2: `gaussPick`, `windowZero`, and the nested split in `window`.

Day 2's `IsTrue`/`decIsTrue` helpers become unused and are deleted (§7).

Recommendation: build `calc` first (stage 1, small), then `rewrite` (stage 2, medium). Close
SW-26 by moving the AoC proofs to `match h: e with`. The questions for the reviewer are in
§10, and the decisions in §11.

## 1. Background: Stitchwort in brief

Stitchwort is a strict, pure, total and dependently typed language, written in Rust. Its main
use is writing library functions, proving things about them, and calling them from a
JavaScript or TypeScript application. Proofs are ordinary terms: there is no tactic language
(DESIGN.md §6, "No tactics"). The compiler also runs in the browser as WebAssembly.

### 1.1 The kernel

A small kernel re-checks everything the elaborator produces.

- It decides definitional equality ("conversion") by evaluating both sides to values and
  comparing them (normalisation by evaluation).
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

Counts in the AoC proofs at commit `8305858`, from `grep -o` **[checked]**. (Draft 1 counted
94 motives and 17 `Bool.inspect`s. Since then, ticket SW-131 moved general lemmas into the
prelude.)

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

Sections 5 to 8 show each example rewritten.

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
- **Preorder chain.** A chain mixing `=` with an order such as `<=` or `<`. It concludes the
  strongest relation that follows: `a = b <= c < d` gives `a < d`.

## 4. How other languages do it

### 4.1 Summary table

| | `calc`-style chains | Relations in a chain | Rewrite with an inferred motive | How the motive is found | Without a known goal | Under binders |
|---|---|---|---|---|---|---|
| **Lean 4** | `calc a` / `_ = b := p` | any, through `Trans` instances; mixes `=`, `<`, `≤` | `rw [p]` (tactic), `h ▸ e` (term) | `kabstract`: keyed matching, compared by conversion | `▸` rewrites the type of `e` instead | `rw` skips subterms that mention a bound variable; `conv`'s `ext` or `simp` goes under binders |
| **Agda** | `begin a ≡⟨ p ⟩ b ∎` (library) | `≡`; `≤-Reasoning` mixes `≡`, `≤`, `<` | `rewrite p` (in a clause) | with-abstraction of the left side in the goal and argument types | n/a (always in a clause) | only occurrences visible after normalising |
| **Idris 2** | `Calc $ \|~ a ~~ b ...(p)` (library) | `=`; `Generic` adds one preorder plus `=` steps | `rewrite p in e` | normalises the goal, then replaces the left side | error: "Can't infer a type for rewrite" | n/a |
| **Rocq** | `transitivity b` (tactic) | relations registered as transitive | `rewrite p` (tactic) | the first match in depth-first order, then every identical subterm | n/a | not inside `forall` (needs `setoid_rewrite`) |
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
  typecheck". It also rejects an equation whose left side is a metavariable ("The pattern to
  be substituted is a metavariable") **[cited:
  [Lean/Meta/Tactic/Rewrite.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean)]**.
- **`kabstract` uses keyed matching.** It compares a subterm with the pattern only when they
  have the same head symbol and number of arguments, and then compares them by `isDefEq`.
  - It skips any subterm that mentions a variable bound inside the goal
    (`if e.hasLooseBVars then visitChildren ()`).
  - Metavariables in the pattern may be instantiated by a match. For matches that are not
    selected, "the metavariable context is rolled back".

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
  (§1.2, §7).

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

- `rewrite H` rewrites left to right, and `<-` reverses it. With a quantified equation, it
  "finds the first matching subterm in depth-first search order. Only subterms identical to
  that first matched subterm are rewritten". It "won't find occurrences inside forall that
  refer to variables bound by the forall", for which there is `setoid_rewrite` **[cited:
  [Rocq reference, equality](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)]**.
- `transitivity b` splits a goal `t = u` (or any relation registered as transitive) into
  `t = b` and `b = u` (same page).

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
- A step with no `:= proof` holds by computation, like Agda's `≡⟨⟩` and Idris's `~=`
  (D33). It elaborates to `rfl`, and it is useful for unfolding a definition so that a later
  `rewrite` can see inside it.
- `calc` is an expression, usable anywhere a proof is: as an argument, in a `let`, or as
  an arm's body.

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
2. Each step's proof is checked against `e(i-1) R ei`. The terms used are the ones elaborated
   from what the user wrote, not their computed forms. A step without a proof is accepted
   when `e(i-1)` and `ei` are equal by conversion.
3. The steps are combined (§5.3) into a proof of `e0 R* en`. `R*` is `<` if any step is `<`,
   else `<=` if any step is `<=`, else `=`.
4. Where a type is expected, `e0 R* en` is unified with it, so `e0` and `en` only need to
   *compute* to the goal's sides. Where no type is expected, the `calc` has type `e0 R* en`.
   So `calc` works in both checking and inferring positions, unlike `rewrite` (§6.4).

I checked that this conversion is enough for the examples in §8. I gave the existing proofs
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
  **[inferred from §1.2]**.
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
rewrite p, q in t           -- `rewrite p in (rewrite q in t)`
rewrite <- p in t           -- right to left: `rewrite (Eq.sym p) in t`
```

Given `p: a = b` and an expected goal `G`:

1. Abstract `a` in `G`, giving `G[x]` with `x` where `a` was.
2. Check that `\x _ => G[x]` is a well-typed motive (`x: A`, where `p` is at type `A`).
3. Check `t` against `G[b]`.
4. Produce `J (\x _ => G[x]) t (Eq.sym p)`. With `Eq.sym p: b = a`, `J` needs a base of type
   `G[b]` and gives `G[a]`, which is `G` up to conversion.

This is Lean's `rw`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's `rewrite`, in the
same direction for all four.

`rewrite p` with no `in` is what a `calc` step usually needs. The step's goal is
`e(i-1) = ei`, both sides as written. Abstracting `a` there and closing with `rfl` works
whether `a` occurs on the left (it becomes `b`) or the right (it becomes `b`, which must then
compute to the left). So `<-` is rarely needed in a `calc`.

For example, in §8 the step from `(Succ highest + n) / Succ highest` to
`(highest + Succ n) / Succ highest` uses `rewrite Nat.addSucc highest n`. That turns the right
side's `highest + Succ n` into `Succ (highest + n)`, which computes to the left side's
`Succ highest + n` (`Nat.add` recurses on its first argument) **[inferred; the step's
equation was checked by ascription, §5.2]**.

Keywords: `calc`, `rewrite` and `in` become reserved. No identifier in the repository's `.sw`
files uses them; they appear only inside strings and comments **[checked: grep]**.

**Implicit arguments in the rule.** If `p`'s left side still contains unsolved implicit
arguments, the first occurrence that matches solves them, as in Lean (§4.2) and Rocq
(§4.5). Later occurrences must then match that instance. A left side that is only a
metavariable is an error, as in Lean (§10, Q5).

### 6.2 Finding occurrences (D36)

Recommended: Lean's keyed matching.

- A subterm of the goal is compared with `a` only if it has the same head (the same
  definition, constructor or variable) and the same number of arguments.
- It is then compared by `matching::same` (syntactic, cheap). If that fails, it is compared
  by conversion under a small budget.
- All matching occurrences are replaced (Lean, Idris and Arend do the same).

Why not purely syntactic matching:

- In `stepLeftFrom` (Example 1), the equation `Nat.modSelf (Succ highest)` is about
  `Succ highest % Succ highest`. The goal says `(Succ highest - 0) % Succ highest`. The two
  are equal by computation, not syntactically.
- The existing occurrence test for `match` is purely syntactic (§1.2). That suits `match`,
  but would make `rewrite` fail on goals like this one.

Which form of the goal is searched:

- In a `calc` step, the step's own elaborated sides.
- Otherwise, the expected type as the elaborator holds it (a value), read back to a term.
  Because definitions unfold lazily (§1.1), this keeps most of the user's structure. It is
  not exactly what was written: `<=` already appears as `Nat.leq a b = True` in messages
  **[checked: the `E-TYPE-MISMATCH` text in §7]**.
- The compiler can already show the type as written in one case only: "when the `rfl` is the
  whole body of a `def` or `theorem` … whose type is the `=`" (`docs/core.md`, error
  messages). It isn't available inside arms or nested terms, so `rewrite` can't rely on it.
- Searching a lightly evaluated goal avoids the Agda and Idris failure where normalising
  destroys the term being looked for (§4.3, §4.4).

### 6.3 What can go wrong, and the messages

- **Nothing found** (Idris's `RewriteNoChange`, Lean's "Did not find an occurrence"):

  ```
  [E-REWRITE-NOTHING] Error: `rewrite` found no `Succ highest % Succ highest` in the goal
    goal: `((highest - j) % Succ highest + n) / Succ highest = (highest - j + n) / Succ highest`
    Note: occurrences are looked for by their outer function (`%`) and compared by computing
    Note: to replace the right side by the left, write `rewrite <- …`
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

  ```
  [E-REWRITE-MOTIVE] Error: replacing `d` everywhere in the goal doesn't give a valid proposition
    `x % d` also needs a proof that `d != 0`, and that proof would no longer match
    Note: rewrite a larger term that contains `d` (such as `x % d`), or state the step with `calc`
  ```

- **Under a binder (D37).** Occurrences of `a` that mention a variable bound inside the goal
  can't be abstracted: `J` can't rewrite inside a function without function extensionality,
  which Stitchwort doesn't have (§1.1). They are skipped, as in Lean and Rocq.

  If nothing else matches, the message points to the pointwise lemmas the AoC proofs already
  use for this. One is `List.mapCongr (f) (g) (h: (x: a) -> f x = g x)`, with type
  `List.map f xs = List.map g xs`; there is also `List.sumByCongr`.

  Occurrences under a binder that don't mention the bound variable are rewritten normally.

### 6.4 When the goal isn't known (D38)

- `rewrite … in` needs an expected type. In an inferring position (the head of an
  application, or a `let` without a type) it is an error that suggests `(rewrite p in t: T)`,
  as Idris does ("Can't infer a type for rewrite").
- Arend's and Lean's `▸` fallback, rewriting in the type of `t` instead, is a possible later
  stage.
- In practice the goal is almost always known, because proof arguments are usually checked
  against a known parameter type. In §8, `headLess` uses `(rewrite <- hl in fromDigitsBound s hd)`
  as an argument whose type is already fixed by the earlier explicit arguments.

### 6.5 Not included

- Rewriting a hypothesis in the context (Lean's `rw … at h`). Today, write
  `rewrite p in h` where `h`'s new type is expected.
- Choosing occurrences (Lean's `occs`, Arend's `{i}`): `calc` with an explicit step covers
  this.
- Matching up to algebra (Arend's `rewriteEq`): that belongs with a reflective arithmetic
  normaliser (`docs/comparisons/aoc-day01.md` §5 item 4).

## 7. SW-26 (`if` case splits): the existing `match h: e with` already solves it (D40)

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
  - This is simpler, but surprising: the branches' goals depend on where the scrutinee
    happens to occur (§10, Q8).

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

## 8. Effect on proof size

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

## 9. Implementation sketch, staging and risks

### Stage 1: `calc` (small; rough guess, two to three days)

- **Lexer.** Add the keywords `calc`, `rewrite` and `in` (reserve all three now).
- **Parser.** Add `Expr::Calc { first, steps, span }`, where each step is
  `{ rel, rhs, proof: Option<Expr>, span }`. Layout follows `docs/syntax.md`: steps are the
  lines indented past the `calc` line, and a proof may continue on further-indented lines.
- **Elaborator** (`check.rs`, plus a new module):
  - infer `e0`, and check each `ei` at its type;
  - build each step's proposition with the existing comparison code (`numbers.rs`);
  - check each proof, or check conversion for a step without one;
  - fold the steps with the §5.3 table;
  - unify the result with the expected type, if there is one.
- **Kernel.** No change. The output is ordinary `Eq.trans`/`J`/`Nat.leTrans` terms, which the
  kernel re-checks.
- **Tests.** Accept: the §8 `calc` texts, plus a `<`/`<=` mix and a chain in an inferring
  position. Reject: each `E-CALC-*` message, as snapshots.

### Stage 2: `rewrite` (medium; rough guess, four to six days)

- **Parser.** Add `Expr::Rewrite { rules: Vec<(reverse, Expr)>, body: Option<Expr>, span }`,
  and the `<-` token.
- **Elaborator, check mode only.**
  - Infer each rule, and insert implicit arguments.
  - Require an `Eq` type. Its left side must not be an unsolved metavariable.
  - Pick the term to search (§6.2).
  - Abstract the rule's left side.
  - Check that the motive is well typed.
  - Check the body against the rewritten goal.
  - Produce `J`.
- **Reuse.** `lift::replace_with` with a hook is already the "replace matching subterms by a
  variable" walk that `let` refolding and `match` generalisation use. The new part is the
  keyed comparison.
- **Tests.**
  - The §8 rewrite-only texts.
  - Each failure mode in §6.3, including the `x % d` `auto` case and an occurrence under a
    binder.
  - A performance test: a rewrite in a goal containing `% 100`, which once took seconds to
    compare (`docs/aoc-2025.md`, day 1). It must stay within budget.

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
  remove that.
- **Cost.** Keyed matching runs a conversion check at each candidate subterm. It needs a
  budget, and a comparison that runs out of budget must count as "no match", not as an error.
- **Messages.** The motive is invisible to the user, so errors must show the goal and what
  was looked for (§6.3), not the motive's raw term.
- **Over-use.** As with Agda, a proof that is a long `rewrite a, b, c, d in rfl` is short but
  hides why it works. The house rule in D41 is the counterweight.
- **DESIGN.md is out of date.** §6 lists `rewrite` among the existing "library functions";
  there is no `rewrite` in the prelude today **[checked: grep]** (D42).

## 10. Questions for the reviewer

These are the points I am least sure of.

1. **Keyed matching versus conversion cost.**
   - Is a conversion check at every same-head subterm affordable in a checker whose
     conversion can unfold arithmetic (`% 100` once took seconds)?
   - Should a candidate that runs out of budget count as "no match" (silent), or be
     reported?
   - Would syntactic matching on the read-back goal, plus `calc` for everything else, be
     enough in practice?
2. **`auto` proofs inside motives.**
   - Is "report an ill-typed motive and suggest rewriting a larger term" the right policy?
   - Or should abstraction treat `auto` arguments specially, for example by re-running the
     search for the abstracted variable in the motive? Lean's error message says `simp` can
     handle "proofs and `Decidable` instances whose types depend on the rewritten term".
   - Is there a sound, simple version of that for Stitchwort?
3. **Under binders.** Is "skip occurrences that mention a bound variable" (Lean, Rocq) right
   for a language with no function extensionality? Or is there a cheap, sound way to do
   better for common cases such as `List.map (\x => …)`?
4. **Soundness of the mixed-relation table (§5.3).** All produced terms are re-checked by
   the kernel, so I believe a mistake can only cause a rejection. Is that right? And is
   "strongest relation wins" (`R*`) the right rule for the conclusion?
5. **Implicit arguments and dot notation in rules.**
   - Rules are elaborated before the goal is searched. For a rule with implicit arguments,
     such as `Eq.sym q` or a lemma with `[x y: a]`, is "solve them at the first match, then
     require the others to match that instance" right? Lean and Rocq do this.
   - Dot notation (`d.move t`) is resolved during elaboration to `Dial.move d t`, so I expect
     matching to see only the resolved form. Are there cases where the user-visible form and
     the matched form differ enough to surprise?
6. **Direction and the `rewrite p` (no `in`) shortcut.** Abstracting in *both* sides of a
   `calc` step's goal and closing by `rfl` makes `<-` rarely needed. Can it rewrite the wrong
   side, or both, in a way that still checks but confuses the reader? Should `rewrite p` in a
   `calc` step search only the left side?
7. **Syntax.**
   - Is Lean's `calc e0` / `_ R e := p` layout the best fit for a language whose other
     syntax is Scala/TypeScript-like?
   - Is reserving `in` acceptable?
   - Is `rewrite p, q in t` clear about its order? It applies `p` first, to the goal.
8. **`match` generalisation surprises.** In `windowZero` (§7), generalising the condition
   also changed what each branch had to prove, because the condition occurred inside the
   goal's definitions after evaluation. Is that expected with-abstraction behaviour, or a
   sign that the occurrence search should be restricted?
9. **Anything unsound, or anything that will surprise users,** anywhere in the note.

## 11. Decisions

Each decision has a stable ID. All are **proposed, awaiting external review**.

| ID | Decision | Recommendation |
|---|---|---|
| D32 | `calc` syntax (§5.1) | Only the aligned form, `calc e0` then `_ R e := proof` lines. Not Lean's `calc e0 = e1 := p` first line, not lines without `_`, not Dafny's alternating lines. |
| D33 | Steps without a proof (§5.1) | Yes: `_ = e` alone means "by computation", like Agda's `≡⟨⟩`. |
| D34 | Relations in a chain (§5.3) | `=`, `<=` and `<` on `Nat`, mixed freely, from a fixed table. `Int` once its transitivity lemmas exist. A user-extensible table later, if ever. |
| D35 | `rewrite` surface (§6.1) | `rewrite p in t`, `rewrite p` (meaning `in rfl`), `rewrite p, q in t`, ASCII `<-` for right to left. Reserve `calc`, `rewrite` and `in` now. |
| D36 | Matching occurrences (§6.2) | Keyed matching from the start: same head and argument count, then syntactic, then conversion under a budget. Search the read-back goal, or a `calc` step's own sides. Rewrite all occurrences. |
| D37 | Under binders (§6.3) | Skip occurrences that mention a bound variable, and point to `List.mapCongr`-style lemmas. No function extensionality. |
| D38 | Goal not known (§6.4) | An error with a type-ascription hint for now. Arend's "rewrite the argument's type instead" possibly in stage 3. |
| D39 | Staging (§9) | `calc` first (small, no new inference, useful at once for `<=` chains), then `rewrite`. |
| D40 | SW-26 (§7) | Close it without new machinery: move the AoC `Bool.inspect` proofs to `match h: e with` (done for six in the experiment), delete `IsTrue`/`decIsTrue`, document the idiom. "Print `if` in goals as `if`" becomes its own ticket. |
| D41 | House style once both exist (§8) | `rewrite` for one to three replacements; `calc` when the intermediate forms help the reader or the chain mixes relations. Then convert the AoC proofs. |
| D42 | DESIGN.md §6 (§9) | Correct the claim that `rewrite` is a library function, and link this note. |

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
- Rocq: [Reasoning with equalities](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html) (`rewrite`, `transitivity`)
- F\*: [wiki, Calculational proofs](https://github.com/FStarLang/FStar/wiki/Calculational-proofs); [ulib/FStar.Calc.fsti](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Calc.fsti)
- Dafny: [Reference manual §8.23, Calc Statement](https://dafny.org/latest/DafnyRef/DafnyRef#sec-calc-statement) ([source](https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Statements.md))
- Arend: [arend-lib StdExtension.java](https://github.com/JetBrains/arend-lib/blob/master/meta/src/main/java/org/arend/lib/StdExtension.java) (`rewrite`, `rewriteI`, `rewriteEq`); [src/Paths.ard](https://github.com/JetBrains/arend-lib/blob/master/src/Paths.ard)
- Stitchwort (repository paths, for the owner; the reviewer doesn't need them):
  - `aoc/src/day01/day01.sw`, `aoc/src/day02/day02.sw`, `aoc/src/day03/day03.sw`
  - `docs/comparisons/aoc-day01.md`, `docs/aoc-2025.md`
  - `docs/core.md`, `docs/syntax.md`, `DESIGN.md` §6
  - `crates/core/src/value.rs`, `crates/elab/src/{check.rs, matching.rs, numbers.rs, prelude.sw}`
  - experiments in a scratch directory, not committed: the `match` versions of six proofs,
    and the ascription checks of every `calc` line in §8

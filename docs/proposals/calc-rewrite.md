# `calc` chains and a `rewrite` term (SW-99), draft 1

**Date:** 19 October 2026. **Ticket:** SW-99 (related: SW-26). **Status:** design note for
review; nothing is implemented.

Labels used below, as in `docs/comparisons/aoc-day01.md`:

- **[checked]**: I ran it, or read it in the source or tool output;
- **[cited]**: taken from the linked documentation or source;
- **[inferred]**: my reasoning from checked facts.

## 0. The short version

Stitchwort proofs are terms, and every equality step is written by hand as
`Eq.trans (Eq.cong (\x => …) lemma) …`. The `\x => …` (the *motive*, §2) repeats the whole
expression around the part that changes. Days 1 to 3 of Advent of Code have 94 such
hand-written motives and 17 `Bool.inspect` motives (§1).

The note proposes two additions. Both elaborate to the terms written today
(`Eq.trans`, `J`, `Nat.leTrans`), so the kernel doesn't change.

1. **`calc`**: a chain of steps, one per line, where each line states the next expression
   and a proof that it follows. This is the same idea as Lean's `calc`, Agda's
   `begin … ≡⟨ p ⟩ … ∎` and Dafny's `calc`. It allows `=`, `<=` and `<` on `Nat` in one
   chain, and it fills in the arguments of `Nat.leTrans` itself.
2. **`rewrite p in t`** (and `rewrite p` alone, which closes the step by computation). The
   motive is found by looking for the left side of `p` in the goal and replacing it. This is
   the mechanism of Lean's `rw`/`▸`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's
   `rewrite`.

Measured on five real lemmas (§7):

- `rewrite` alone makes them 31 to 45% shorter.
- `calc` makes them about as long as now, and sometimes longer. Every intermediate
  expression is written out and checked, so a reader can follow the proof line by line.
- `calc` is 29% shorter on the `<=` chain, because it fills in `Nat.leTrans`'s arguments.

**SW-26 needs neither.** The existing `match h: e with` already does Agda-style
*with-abstraction*. I replaced four `Bool.inspect` proofs with it (day 3's `pickGe`, `pickLen`
and `pickSub`, and day 2's `gaussPick`), and all four check. Day 2's `IsTrue`/`decIsTrue`
helpers became unused and could be deleted (§6) **[checked]**.

Recommendation: build `calc` first (stage 1, small), then `rewrite` (stage 2, medium). Close
SW-26 by moving the AoC proofs to `match h: e with`. The decisions are in §9.

## 1. The problem, with real examples

Counts in the AoC proofs, from `grep -o` (occurrences) **[checked]**:

| | `Eq.trans` | `Eq.cong` | `Eq.cong (\…` (hand-written motive) | `Eq.sym` | `J (` | `Bool.inspect` | `Nat.leTrans` | `Nat.le/ltCong…` |
|---|---|---|---|---|---|---|---|---|
| day 1 | 52 | 51 | 46 | 21 | 3 | 2 | 2 | 0 |
| day 2 | 62 | 53 | 45 | 29 | 5 | 10 | 15 | 10 |
| day 3 | 10 | 5 | 3 | 12 | 1 | 5 | 8 | 17 |

(The ticket's 43/45 and 60/51 are `grep -c` line counts of the same files.)

**Example 1, a chain of rewrites** (day 1, `stepLeftFrom`, first case):

```
  | Zero,   h, n =>
    Eq.trans (Eq.cong (\x => Succ ((x + n) / Succ highest)) (Nat.modSelf (Succ highest)))
      (Eq.sym (Eq.trans (Eq.cong (\x => (x + Succ n) / Succ highest) (Nat.modSmall highest (Succ highest) (Nat.leRefl highest)))
        (Eq.trans (Eq.cong (\x => x / Succ highest) (Nat.addSucc highest n)) (Nat.addDivSelf (Succ highest) n))))
```

This case makes three replacements and uses one division fact. Most of the text is the three
motives (`\x => Succ ((x + n) / Succ highest)` and so on). The intermediate expressions are
never written down, and the chain runs backwards from the right side (`Eq.sym (Eq.trans …)`).

**Example 2, a long chain** (day 2, `writeTimesMul`): seven steps nested seven deep:

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

**Example 3, an inequality chain** (day 3, `headLess`). Each `Nat.leCongLeft`,
`Nat.leCongRight` and `Nat.leTrans` takes the three numbers explicitly:

```
  Nat.leCongLeft (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (Nat.fromDigits (Cons y s)) (Nat.fromDigits (Cons t r))
    (Eq.sym (fromDigitsConsLen y s r hl))
    (Nat.leCongRight (y * Nat.pow 10 (List.length r) + Nat.fromDigits s) (t * Nat.pow 10 (List.length r) + Nat.fromDigits r) (Nat.fromDigits (Cons t r))
      (Eq.sym (Nat.fromDigitsCons t r))
      (headLessArith y t (Nat.pow 10 (List.length r)) (Nat.fromDigits s) (Nat.fromDigits r)
        (Nat.ltCongRight (Nat.fromDigits s) (Nat.pow 10 (List.length s)) (Nat.pow 10 (List.length r)) (Eq.cong (\n => Nat.pow 10 n) hl) (fromDigitsBound s hd))
        h))
```

**Example 4, a case split on an `if`** (day 3, `pickGe`, SW-26). The motive restates the goal
with the `if` spelled out as the checker sees it:

```
    Bool.inspect (Nat.leq (Succ c) x)
      (\b => c <= Pair.fst (Decidable.elim (Bool.decTrue b) (\u => Bank.best.pick w more x more) (\u => Bank.best.pick w more c after)))
      (\e => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more))
      (\e => pickGe w more c after)
```

Sections 4 to 6 show each example rewritten.

## 2. Terms used

- **Motive.** A function that says *where* in a proposition the change happens. To turn a
  proof of `P a` into a proof of `P b` using `a = b`, you need `P` itself, the "motive".
  Today you write it: `\x => (x + n) / Succ highest`.
- **`J`** is Stitchwort's primitive for using an equation. `J motive base p` turns `base`,
  a proof of `motive x rfl`, into a proof of `motive y p`, given `p: x = y`. `Eq.cong`,
  `Eq.sym` and `Eq.trans` are defined with it (`crates/elab/src/prelude.sw:148-152`).
- **Transport** means using `J` (or `Eq.cong`) to move a proof along an equation.
- **Abstraction** is finding every occurrence of a term in an expression and replacing it
  with a variable. This is how other systems compute a motive. With goal
  `((a + 1) % d + n) % d = …` and equation `(a + 1) % d = 0`, abstracting `(a + 1) % d`
  gives the motive `\x => (x + n) % d = …`.
- **Conversion** means two terms are equal by computing, for example `0 + n` and `n`. The
  checker compares types this way. A `calc` line or a `rewrite` may therefore differ from the
  goal as long as it computes to the same thing.
- **Preorder chain.** A chain mixing `=` with an order such as `<=` or `<`. It concludes the
  strongest relation that follows: `a = b <= c < d` gives `a < d`.

## 3. How other languages do it

### 3.1 Summary table

| | `calc`-style chains | Relations in a chain | Rewrite with an inferred motive | How the motive is found | Without a known goal | Under binders |
|---|---|---|---|---|---|---|
| **Lean 4** | `calc a` / `_ = b := p` | any, through `Trans` instances; mixes `=`, `<`, `≤` | `rw [p]` (tactic), `h ▸ e` (term) | `kabstract`: every subterm with the same head and argument count as the left side, compared by conversion | `▸` rewrites the type of `e` instead | `rw` skips subterms that mention a bound variable; `conv`'s `ext` or `simp` goes under binders |
| **Agda** | `begin a ≡⟨ p ⟩ b ∎` (library) | `≡`; `≤-Reasoning` mixes `≡`, `≤`, `<` | `rewrite p` (in a clause) | with-abstraction of the left side in the goal and argument types | n/a (always in a clause) | only occurrences visible after normalising |
| **Idris 2** | `Calc $ \|~ a ~~ b ...(p)` (library) | `=`; `Generic` adds one preorder plus `=` steps | `rewrite p in e` | normalises the goal, then replaces the left side | error: "Can't infer a type for rewrite" | n/a |
| **Rocq** | `transitivity b` (tactic) | relations registered as transitive | `rewrite p` (tactic) | the first match in depth-first order, then every identical subterm | n/a | not inside `forall` (needs `setoid_rewrite`) |
| **F\*** | `calc (rel) { a; == { p } b; … }` | any; the SMT solver checks that they combine | n/a (SMT) | n/a | n/a | n/a |
| **Dafny** | `calc { a; == { hint } b; … }` | chain-compatible operators; one `!=` with `==` | n/a (verifier) | n/a | n/a | n/a |
| **Arend** | `a ==< p >== b `qed`` (library) | `=` | `rewrite p t`, `rewriteI p t` (term) | replaces occurrences of the left side in the expected type | rewrites the type of `t` instead | not checked |

### 3.2 Lean 4

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
  typecheck" **[cited:
  [Lean/Meta/Tactic/Rewrite.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Rewrite.lean)]**.
- **`kabstract` uses keyed matching.** It compares a subterm with the pattern only when they
  have the same head symbol and number of arguments, and then compares them by `isDefEq`
  (conversion). It skips any subterm that mentions a variable bound inside the goal
  (`if e.hasLooseBVars then visitChildren ()`). That is why `rw` can't rewrite `x + 0` inside
  `fun x => …` **[cited:
  [Lean/Meta/KAbstract.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/KAbstract.lean)]**.
  The reference says `conv` exists for rewrites "underneath a binder that prevents tactics like
  rw from accessing the term", and for picking one part of a goal **[cited:
  [reference, `conv`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Targeted-Rewriting-with--conv/)]**.
- **Pitfalls.**
  - "motive is not type correct". Mathlib's example is
    `example (h : [5] ≠ []) : List.getLast [5] h = 5 := by rw [show [5] = [5] from rfl]`:
    replacing `[5]` everywhere also changes the type of the proof `h` **[cited:
    [Mathlib KAbstractPositions](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Lean/Meta/KAbstractPositions.html)]**.
  - Choosing occurrences needs `rw (occs := .pos [2])` **[cited:
    [reference, `rewrite`](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/#rewrite)]**.
  - `←` reverses the direction (same source).
- **The general version: `@[elab_as_elim]`.** Lean elaborates a function whose result is
  `motive x₁ … xₙ` "by matching `p x₁ … xₙ` against the expected type, then replacing `xₙ`
  through `x₁` … with variables". It fails if "the expected type cannot be determined"
  **[cited:
  [Lean/Elab/App.lean](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/App.lean),
  the `elab_as_elim` docstring]**. This is how a `Bool.inspect` with an omitted motive could
  work (§6).

### 3.3 Agda

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

  Writing the day 1 port, I hit two more **[checked, aoc-day01.md §3.2]**:
  - `rewrite` fails on an equation with an instance argument;
  - it fails when the goal has already reduced past the term.
- **`with … in eq`** names the equation between the scrutinee and the new variable **[cited:
  same page, "With-abstraction equality"]**. Stitchwort's `match h: e with` is the same idea
  (§6).

### 3.4 Idris 2

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
- **Pitfall.** Normalising the goal is what broke `Calc` steps in the day 1 port, once
  `modNatNZ` unfolded into `mod'` **[checked, aoc-day01.md §3.3]**.

### 3.5 Rocq (Coq)

- `rewrite H` rewrites left to right, and `<-` reverses it. With a quantified equation, it
  "finds the first matching subterm in depth-first search order. Only subterms identical to
  that first matched subterm are rewritten". It "won't find occurrences inside forall that
  refer to variables bound by the forall", for which there is `setoid_rewrite` **[cited:
  [Rocq reference, equality](https://rocq-prover.org/doc/master/refman/proofs/writing-proofs/equality.html)]**.
- `transitivity b` splits a goal `t = u` (or any relation registered as transitive) into
  `t = b` and `b = u`. This is the tactic version of one `calc` step (same page).

### 3.6 F\*

- `calc (>) { a + a; == {} 2 * a; > { lem1 a } a; }`. Each step has a relation and a
  justification in braces. F\* checks that the step relations combine into the overall one
  ("if `a == b > c`, then `a > c`"), and "this condition is currently sent to the SMT solver"
  **[cited: [F\* wiki, Calculational proofs](https://github.com/FStarLang/FStar/wiki/Calculational-proofs)]**.
- The library behind it keeps the list of step relations and checks `calc_chain_compatible`
  against the conclusion **[cited:
  [ulib/FStar.Calc.fsti](https://github.com/FStarLang/FStar/blob/master/ulib/FStar.Calc.fsti)]**.
  With no SMT solver, Stitchwort would need a fixed table instead (§4.3).

### 3.7 Dafny

- `calc { e0; == { hint } e1; … }`, or `calc == { … }` to give a default operator ("If that
  operator is omitted, it defaults to equality").
- Only "chain-compatible operators can be used together", and "a single occurrence of the
  intransitive operator `!=`" may appear in a chain of equalities.
- The hints are statements (lemma calls, nested `calc`s) that help the verifier prove that
  step **[cited:
  [Dafny reference §8.23](https://dafny.org/latest/DafnyRef/DafnyRef#sec-calc-statement);
  source
  [docs/DafnyRef/Statements.md](https://github.com/dafny-lang/dafny/blob/master/docs/DafnyRef/Statements.md)]**.

### 3.8 Arend

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

### 3.9 What to take from the survey

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

## 4. `calc` for Stitchwort

### 4.1 Syntax

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
- A step with no `:= proof` holds by computation, like Agda's `≡⟨⟩` and Idris's `~=`. It
  elaborates to `rfl`, and it is useful for unfolding a definition so that a later
  `rewrite` can see inside it.
- `calc` is an expression, usable anywhere a proof is: as an argument, in a `let`, or as
  an arm's body.

Alternatives (decision C1):

- **(b)** Lean's other first line, `calc e0 = e1 := p` followed by `_ = …` lines. This
  gives two ways to write the same chain.
- **(c)** Drop the `_`: lines read `= e1 := p`. It is shorter, but a line starting with an
  operator is new to Stitchwort's layout (`docs/syntax.md` lets `|>`, `then` and `else` start
  lines, but not `=`).
- **(d)** Dafny's layout, with expressions and relations on alternate lines. It is longer, and
  the reasons sit on the relation lines.

### 4.2 What is checked

1. `e0` is inferred. Each `ei` is checked against the type of `e0`.
2. Each step's proof is checked against `e(i-1) R ei`. The terms used are the ones elaborated
   from what the user wrote, not their computed forms. A step without a proof is accepted
   when `e(i-1)` and `ei` are equal by conversion.
3. The steps are combined (§4.3) into a proof of `e0 R* en`. `R*` is `<` if any step is `<`,
   else `<=` if any step is `<=`, else `=`.
4. Where a type is expected, `e0 R* en` is unified with it, so `e0` and `en` only need to
   *compute* to the goal's sides. Where no type is expected, the `calc` has type `e0 R* en`.
   So `calc` works in both checking and inferring positions, unlike `rewrite` (§5.4).

I checked that this conversion is enough for the examples in §7. I gave the existing proofs
type ascriptions `(p: e0 = e1)` with exactly the intermediate expressions used there, and the
real checker accepted them. Two examples:

- the first line `Succ ((Succ highest % Succ highest + n) / Succ highest)` is accepted where
  the goal says `Bool.toNat (0 == 0) + ((Succ highest - 0) % Succ highest + n) / Succ highest`;
- `_ _` holes in `List.occurrencesAppend Dial.isZero _ _` are solved from the step's type
  **[checked]**.

### 4.3 Combining steps

There is no type-class mechanism, so the elaborator uses a fixed table. `R1` is the relation
proved so far, from `a` to `b`; `R2` is the new step, from `b` to `c`.

| `R1` then `R2` | Result | Term produced |
|---|---|---|
| `=`, `=` | `=` | `Eq.trans p q` |
| `=`, any `R` | `R` | `J (\w _ => w R c) q (Eq.sym p)` |
| any `R`, `=` | `R` | `J (\w _ => a R w) p q` |
| `<=`, `<=` | `<=` | `Nat.leTrans a b c p q` |
| `<`, `<=` | `<` | `Nat.leTrans (Succ a) b c p q` |
| `<=`, `<` | `<` | `Nat.leTrans (Succ a) (Succ b) c p q` |
| `<`, `<` | `<` | `Nat.lessTrans …` |

- The `=` rows are Lean's `Trans Eq r r` and `Trans r Eq r` instances, written with `J`.
- The `Nat` rows rely on `a < b` being `Nat.leq (Succ a) b = True`
  (`prelude.sw:109`), and on `Nat.leq (Succ a) (Succ b)` computing to `Nat.leq a b`.
  So no new lemmas are needed.

I checked `<=`/`<`, `<`/`<=`, `=`/`<=` and `<=`/`=` as plain theorems (`leLt`, `ltLe`,
`eqLe`, `leEq`) **[checked]**.

- `Int` chains need `Int.leTrans`-style lemmas first; the prelude has none
  (`grep '^theorem .*Trans'` lists only `Eq.trans`, `Nat.leTrans`, `Nat.lessTrans`,
  `List.permTrans`) **[checked]**.
- `>`/`>=` and mixed directions are an error, as in Dafny.
- `!=` is out of scope.
- A user-extensible table (for `List.Perm`, or a user's own order) would need a way to
  register a transitivity lemma (decision C3).

### 4.4 Error messages

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

## 5. `rewrite` for Stitchwort

### 5.1 Syntax and meaning

```
rewrite p in t              -- t proves the goal with p's left side replaced by its right side
rewrite p                   -- the same as `rewrite p in rfl`
rewrite p, q in t           -- `rewrite p in (rewrite q in t)`
rewrite <- p in t           -- right to left: `rewrite (Eq.sym p) in t`
```

Given `p: a = b` and an expected goal `G`:

1. Abstract `a` in `G`, giving `G[x]` with `x` where `a` was.
2. Check `t` against `G[b]`.
3. Produce `J (\x _ => G[x]) t (Eq.sym p)`, which has type `G[a]`, that is, `G`.

This is Lean's `rw`, Agda's `rewrite`, Idris's `rewrite … in` and Arend's `rewrite`, in the
same direction for all four.

`rewrite p` with no `in` is what a `calc` step usually needs. The step's goal is
`e(i-1) = ei`, both sides as written. Abstracting `a` there and closing with `rfl` works
whether `a` occurs on the left (it becomes `b`) or the right (it becomes `b`, which must then
compute to the left). So `<-` is rarely needed in a `calc`: in §7, `Nat.addSucc highest n`
turns `(highest + Succ n)` on the right side into `Succ (highest + n)`, which computes to the
left side's `(Succ highest + n)` **[inferred from the checked ascriptions in §4.2]**.

Keywords: `calc`, `rewrite` and `in` become reserved. No identifier in the repository's `.sw`
files uses them; they appear only inside strings and comments **[checked: grep]**.

### 5.2 Finding occurrences

Recommended: Lean's keyed matching (decision R2).

- A subterm of the goal is compared with `a` only if it has the same head (the same
  definition, constructor or variable) and the same number of arguments.
- It is then compared by `matching::same` (syntactic, cheap). If that fails, it is compared
  by conversion under a small budget, with no metavariables solved.
- All matching occurrences are replaced (Lean, Idris and Arend do the same).

Why not purely syntactic matching:

- In `stepLeftFrom`, the equation `Nat.modSelf (Succ highest)` is about
  `Succ highest % Succ highest`, but the goal as written says
  `(Succ highest - 0) % Succ highest`. The two are equal by computation, not syntactically.
- The existing occurrence test for `match` generalisation is purely syntactic
  (`crates/elab/src/matching.rs:529`, "No definitions are unfolded") **[checked]**. That suits
  `match`, but would make `rewrite` fail on goals like this one.

What is searched:

- In a `calc` step, the step's own elaborated sides.
- Otherwise, the expected type as the elaborator holds it, quoted back to a term.
- If the definition's type as written is available (`Ctx::goal`, `check.rs:52`), it is
  preferred. Error messages already use it, so they show `Nat.mod (Succ h - 0) (Succ h)`
  where the computed form is a long `Nat.divFuel …` term **[checked: the `E-REFL` message
  for a probe file]**.
- Searching a lightly evaluated goal avoids the Agda and Idris failure where normalising
  destroys the term being looked for (§3.3, §3.4).

### 5.3 What can go wrong, and the messages

- **Nothing found** (Idris's `RewriteNoChange`, Lean's "Did not find an occurrence"):

  ```
  [E-REWRITE-NOTHING] Error: `rewrite` found no `Succ highest % Succ highest` in the goal
    goal: `((highest - j) % Succ highest + n) / Succ highest = (highest - j + n) / Succ highest`
    Note: occurrences are looked for by their outer function (`%`) and compared by computing
    Note: to replace the right side by the left, write `rewrite <- …`
  ```

- **The motive is ill typed** (Lean's "motive is not type correct", Agda's ill-typed
  with-abstraction). In Stitchwort the likely cause is an `auto` argument. `x % d` carries a
  proof of `d != 0`, so rewriting `d` leaves that proof about the wrong number. The day 1
  notes already show that `auto` proofs found in different places are different terms
  (`docs/aoc-2025.md`, "auto proofs differ by context") **[checked]**.

  ```
  [E-REWRITE-MOTIVE] Error: replacing `d` everywhere in the goal doesn't give a valid proposition
    `x % d` also needs a proof that `d != 0`, and that proof would no longer match
    Note: rewrite a larger term that contains `d` (such as `x % d`), or state the step with `calc`
  ```

- **Under a binder.** Occurrences of `a` that mention a variable bound inside the goal can't
  be abstracted, since `J` can't rewrite inside a function without function extensionality,
  which Stitchwort doesn't have. They are skipped, as in Lean and Rocq. If nothing else
  matches, the message points to the pointwise lemmas the AoC proofs already use for this
  (`List.mapCongr`, `List.sumByCongr`, in day 2's `specWindow` and `multiplierSucc`).
  Occurrences under a binder that don't mention the bound variable are rewritten normally.

### 5.4 When the goal isn't known

- `rewrite … in` needs an expected type. In an inferring position (the head of an
  application, or a `let` without a type) it is an error that suggests `(rewrite p in t: T)`,
  as Idris does ("Can't infer a type for rewrite").
- Arend's and Lean's `▸` fallback, rewriting in the type of `t` instead, is a possible later
  stage (decision R4).
- In practice the goal is almost always known: proof arguments are usually checked against a
  known parameter type. `headLess` in §7 uses `(rewrite <- hl in fromDigitsBound s hd)` as an
  argument whose type is already fixed by the earlier arguments.

### 5.5 Not included

- Rewriting a hypothesis in the context (Lean's `rw … at h`). Today, write
  `rewrite p in h` where `h`'s new type is expected.
- Choosing occurrences (Lean's `occs`, Arend's `{i}`): `calc` with an explicit step covers
  this.
- Matching up to algebra (Arend's `rewriteEq`): that belongs with the normaliser in
  aoc-day01.md §5 item 4.

## 6. SW-26 (`if` case splits): the existing `match h: e with` already solves it

- `match h: e with` generalises `e`: it replaces occurrences of `e` in the expected type,
  and in the types of variables in scope, by the new variable, and binds `h: e = s`
  (`crates/elab/src/matching.rs:1-19`; `docs/syntax.md:457`) **[checked]**.
- That is Agda's `with … in eq`, and it is exactly the motive `Bool.inspect` asks for.
- The occurrence test is syntactic, but that suits this case: the `if` elaborates to
  `Decidable.elim (Bool.decTrue (Nat.leq (Succ c) x)) …`, which contains the scrutinee
  `Nat.leq (Succ c) x` as written.

I replaced four `Bool.inspect` proofs in copies of the AoC files and checked them with the
release build of `stitchwort check` **[checked]**:

- `pickGe`, `pickLen` and `pickSub` (day 3);
- `gaussPick` (day 2), after which I also deleted `IsTrue` and `decIsTrue`.

To confirm the checker was really checking, I put a wrong argument in one branch, and it was
rejected with `E-TYPE-MISMATCH`. Check times were unchanged (0.13 s for day 3, 0.27 s for
day 2).

Before (`pickGe`, Example 4 above, 5 lines) and after:

```
  | Succ w, Cons x more, c, after =>
    match e: Nat.leq (Succ c) x with
      | True  => Nat.leTrans c x (Pair.fst (Bank.best.pick w more x more)) (Nat.lessLe c x e) (pickGe w more x more)
      | False => pickGe w more c after
```

`pickSub` is the strongest case. Its motive is a whole implication mentioning the `if` twice,
and the hypothesis `h` was passed through `Bool.inspect` by hand. With `match`, `h`'s type is
generalised automatically and the branches use `h` directly.

So SW-26 needs no new elaborator feature. The work left is to:

- move the AoC proofs (17 `Bool.inspect`s in days 1 to 3) to `match h: e with`;
- delete `IsTrue`/`decIsTrue`;
- add a sentence to `docs/syntax.md` saying this is how to split on an `if` in a proof.

The ticket's other idea, printing `if` in goals as `if`, is separate and still worthwhile.

**Could `rewrite`'s machinery do it instead?**

- Lean's `@[elab_as_elim]` (§3.2) would let `Bool.inspect b _ t f` infer its motive by
  abstracting `b` in the goal, the same abstraction `rewrite` uses.
- I don't recommend it now: `match` already covers the cases, and an attribute is new
  surface area.
- If `rewrite` lands, the keyed matcher could later replace `match`'s syntactic test, so that
  generalisation also finds `e` up to computation.

## 7. Effect on proof size

I rewrote five real lemmas by hand. Sizes are characters with runs of spaces and newlines
squeezed to one, comments and blank lines removed, as in aoc-day01.md.

- Before: the files on `main`.
- After: the texts below. They are not runnable today, but every `calc` line's intermediate
  expression was checked by the ascription method of §4.2 **[checked]**.
- The rewrite-only versions also need keyed matching (§5.2) **[inferred]**.

| Lemma | Now | With `calc` | With `rewrite` only |
|---|---|---|---|
| `stepLeftFrom` (day 1) | 1,025 | 1,228 (+20%) | 709 (−31%) |
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
  `<=` chains it is shorter, because it fills in `Nat.leTrans`'s three explicit arguments,
  which day 2 and day 3 spell out 23 times.
- **Used together**, `calc` with `rewrite` steps makes long chains readable and short chains
  short. A reasonable house rule: `rewrite` for one to three replacements, and `calc` when a
  reader needs to see the intermediate forms or the chain mixes `=` with `<=`/`<`
  (decision G1).

## 8. Implementation sketch, staging and risks

### Stage 1: `calc` (small; rough guess, two to three days)

- **Lexer.** Add the keywords `calc`, `rewrite` and `in` (reserve all three now).
- **Parser.** Add `Expr::Calc { first, steps, span }`, where each step is
  `{ rel, rhs, proof: Option<Expr>, span }`. Layout follows `docs/syntax.md`: steps are the
  lines indented past the `calc` line, and a proof may continue on further-indented lines.
- **Elaborator** (`check.rs`, a new `calc.rs` like `pipe.rs`/`logic.rs`):
  - infer `e0`, and check each `ei` at its type;
  - build each step's proposition with the existing comparison code (`numbers.rs`, which
    already turns `<=`/`<` into `Nat.LessEq`/`Nat.LessThan`);
  - check each proof, or check conversion for a step without one;
  - fold the steps with the §4.3 table;
  - unify the result with the expected type, if there is one.
- **Kernel.** No change. The output is ordinary `Eq.trans`/`J`/`Nat.leTrans` terms, which the
  kernel re-checks (DESIGN.md §6; the trusted base is unchanged).
- **Tests.** Accept: the §7 `calc` texts, plus a `<`/`<=` mix and a chain in an inferring
  position. Reject: each `E-CALC-*` message as a snapshot.
- **Migration.** Convert a handful of AoC lemmas as a real-use check.

### Stage 2: `rewrite` (medium; rough guess, four to six days)

- **Parser.** Add `Expr::Rewrite { rules: Vec<(reverse, Expr)>, body: Option<Expr>, span }`,
  and the `<-` token.
- **Elaborator, check mode only.**
  - Infer each rule, and insert implicit arguments.
  - Require an `Eq` type. Its left side must not be an unsolved metavariable (Lean's check).
  - Pick the term to search: the `calc` step's elaborated sides, else `Ctx::goal` if it
    applies, else the quoted expected type.
  - Abstract the rule's left side.
  - Check that the abstracted motive is a well-typed `Prop` (`E-REWRITE-MOTIVE`).
  - Check the body against the rewritten goal.
  - Produce `J`.
- **Reuse.** `lift::replace_with` with a hook is already the "replace matching subterms by a
  variable" walk that `let` refolding (`unify.rs:494`) and `match` generalisation use. The new
  part is the keyed comparison.
- **Tests.**
  - The §7 rewrite-only texts.
  - Each failure mode in §5.3, including the `x % d` `auto` case and an occurrence under a
    binder.
  - A performance test: a rewrite in a goal containing `% 100`, which once took seconds to
    compare (aoc-day01 notes). It must stay within budget.

### Stage 3 (later, if wanted)

- Rewrite in the body's own type when no goal is known (Arend's and `▸`'s behaviour).
- Choosing occurrences.
- Keyed matching for `match` generalisation.
- `Int` order lemmas, so `calc` works on `Int`.

### Risks

- **Which form of the goal is searched.** If it is too evaluated, the term isn't found (the
  Agda and Idris failures). If it is too literal, an equal-by-computation term isn't found.
  Keyed matching plus the written goal is the mitigation, and the tests above are the check.
- **`auto` arguments.** These are the most likely cause of ill-typed motives (§5.3). Two
  occurrences of `x % d` with different `ok` proofs may also fail to match. This existing
  friction (no proof irrelevance) shows up here first. The
  [proof-irrelevance proposal](proof-irrelevance.md) would remove it.
- **Cost.** Keyed matching runs a conversion check at each candidate subterm. It needs a
  budget (`unify::cheaply` is a model), and a failed comparison must count as "no match", not
  as an error.
- **Messages.** The motive is invisible to the user, so errors must show the goal and what
  was looked for (§5.3), not the motive's raw term.
- **Over-use.** As with Agda, a proof that is a long `rewrite a, b, c, d in rfl` is short but
  hides why it works. The house rule in decision G1 is the counterweight.
- **DESIGN.md is out of date.** §6 lists `rewrite` among the existing "library functions";
  there is no `rewrite` in the prelude today **[checked: grep]**. The text should be updated
  whichever way this goes.

## 9. Decisions for Matt

1. **C1, `calc` syntax.** Recommend the aligned form, `calc e0` then `_ R e := proof` lines
   (Lean's second form), as the only form. Alternatives: Lean's
   `calc e0 = e1 := p` first line as well; lines without `_`; Dafny's alternating lines
   (§4.1).
2. **C2, steps without a proof.** Recommend yes: `_ = e` alone means "by computation", like
   Agda's `≡⟨⟩`.
3. **C3, relations.** Recommend `=`, `<=` and `<` on `Nat`, mixed freely, from a fixed table
   (§4.3). `Int` comes after its transitivity lemmas exist. A user-extensible table comes
   later, if ever.
4. **R1, `rewrite` surface.**
   - `rewrite p in t`, `rewrite p` (meaning `in rfl`), `rewrite p, q in t`, and `<-` for
     right to left.
   - Reserve `calc`, `rewrite` and `in` now.
   - Recommend ASCII `<-` only, matching `->` and `=>`.
5. **R2, matching occurrences.** Recommend keyed matching from the start: same head and
   argument count, then syntactic, then conversion under a budget. Search the written or
   lightly evaluated goal, and rewrite all occurrences. Alternative: syntactic only at first,
   which is cheaper but fails on day 1's `(Succ highest - 0) % …`.
6. **R3, under binders.** Recommend skipping occurrences that mention a bound variable and
   pointing to `List.mapCongr`-style lemmas, as Lean and Rocq do. No function
   extensionality.
7. **R4, unknown goal.** Recommend an error with a type-ascription hint for now. Arend's
   "rewrite the argument's type instead" could come in stage 3.
8. **S1, staging.** Recommend `calc` first (small, no new inference, useful at once for
   `<=` chains), then `rewrite`. Alternative: `rewrite` first, since it gives most of the
   size saving, at more risk.
9. **SW-26.** Recommend closing it without new machinery:
   - move the AoC `Bool.inspect` proofs to `match h: e with` (verified on four lemmas);
   - delete `IsTrue`/`decIsTrue`;
   - document the idiom in `docs/syntax.md`;
   - keep "print `if` in goals as `if`" as its own small ticket.
10. **G1, house style once both exist.** Recommend `rewrite` for one to three replacements,
    and `calc` when the intermediate forms help the reader or the chain mixes relations. Then
    convert the AoC proofs (DeepSeek-sized work once the features exist).
11. **D1, DESIGN.md §6.** Recommend correcting the claim that `rewrite` is a library function,
    and linking this note.

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
- Stitchwort:
  - `aoc/day01.sw`, `aoc/day02.sw`, `aoc/day03.sw`
  - `docs/comparisons/aoc-day01.md`, `docs/aoc-2025.md`
  - `crates/elab/src/{check.rs, matching.rs, unify.rs, numbers.rs, prelude.sw}`
  - experiments in a scratch directory, not committed: the `match` versions of four lemmas
    and the ascription checks of every `calc` line in §7

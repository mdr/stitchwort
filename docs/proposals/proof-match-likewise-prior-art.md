# One proof for several cases: what other systems do

**Status:** prior-art survey, 19 November 2026 (SW-4228, a Fable paper lane),
for D3694 and `docs/proposals/proof-match-likewise.md` (SW-4219, "the
note" below). Nothing is built. It confirms the note's Design 2 with four
amendments (§4) and restates D3694 (§5).

Claims are marked **[measured]** (a probe run today; versions and probe
texts in §6), **[read]** (a manual or source file read today, cited) or
**[recalled]** (not re-checked; treat as likely, not certain).

## In plain words

**The question.** D3694 would let `| Inl same | Inr same => body` bind
`same` in both alternatives and check `body` once for each, so `same` may be
`text = "&&"` in one and `text = "∧"` in the other. Is that normal, and
what can a body do with a name that has two types?

**What others do.** It splits cleanly by kind of language:

- **Programming languages give the name one type.** OCaml, Rust and Swift
  let alternatives bind names, but each name must have the same type in
  every alternative, and the body is checked once [read; OCaml measured].
  Haskell (GHC 9.12), Scala today and Dafny don't let alternatives bind
  names at all [read; Haskell measured]. That is where Stitchwort's current rule came from.
- **The two big provers whose proofs can be terms do exactly what D3694
  proposes.** Lean 4 and Rocq both copy the body under each alternative
  and check each copy on its own, and both accept a name with a different
  type in each [measured, both]. Lean's own textbook says so: "the result
  expression is simply duplicated across each pattern" [read]. F* copies
  the branch per alternative too [read, source]. So Design 2 is not a new
  idea: it is Rocq's rule almost exactly.
- **The rest have no or-patterns and use tactics instead.** Agda and
  Idris 2 have none [measured]; Isabelle's `case` names one case [read].
  Their users write "split, then run this on every case": Lean's
  `cases t <;> tac`, Rocq's `destruct t; tac`, Isabelle's
  `by (cases t; simp)`. Stitchwort's catch-all arm after a split is already
  that, written as a term.

**What you can do in the body.** Exactly what you could do if you pasted the
body under each alternative by hand, because that is what the checker
does. In practice that means handing the name to something that works for
either type:

```
| Inl (Inl same) | Inl (Inr same) => Both (rewrite same) (rewrite same)
```

`rewrite same` works whichever equation `same` is. Lean's version, in a
program: `| .inl x | .inr x => toString x` with `x` a number in one
alternative and a string in the other; each copy picks its own `toString`
[measured]. What you can't do is something that fits only one of the types:
`| .inl x | .inr x => x + 1` fails, in the alternative where `x` is a
string [measured]. Nothing new can go wrong at run time or in a proof: the
result is the same term as the arms written out.

**Where the others stumble, and what to take from it.** Lean's version has
three rough edges, all measured: it doesn't check that the alternatives
bind the same names; an error in one alternative doesn't say which one;
and an error in all of them is printed once per alternative at the same
spot. Lean's textbook warns that "there is a potential for confusing
behavior". Rocq checks the names, as Design 2 does. So the recommendation
is **Design 2, confirmed, with the alternative-naming error note made part
of it rather than a separate nicety** (§4).

## 1. Comparison

"Per alternative" means the body is checked once for each alternative, with
that alternative's types; "shared" means once, with one type for each name.

| System | Or-patterns in terms | May bind names | Types of a bound name | Nested | Usual way to share a proof over cases |
|---|---|---|---|---|---|
| **Lean 4** (4.35.0) | yes, `\| p \| q => e` | yes; same names *not* checked | per alternative [measured; read, source] | no: parse error [measured] | `cases t <;> tac`, `all_goals`, `case a \| b =>`, `cases t with \| a \| b => tac`, `rcases h with h \| h <;> tac` [measured] |
| **Rocq** (9.1.1) | yes | yes; same names required | per alternative [measured] | yes [read, manual] | `destruct t; tac`, `tac; [t1 \| t2]`, `destruct h as [h \| h]`; ssreflect `case: h => [h\|h]`, `by case: t` [measured] |
| **F\*** | yes | yes; same names required | one branch per alternative [read, source; not probed] | [not checked] | SMT does most case work; `match` in lemma bodies [recalled] |
| **Agda** (2.8.0) | no [measured] | – | – | – | a helper lemma; catch-all clauses; pattern-matching lambdas [recalled] |
| **Idris 2** (0.8.0) | no [measured] | – | – | – | helper lemmas; catch-all clauses [recalled] |
| **Isabelle/Isar** | no: `case` takes one name [read] | – | – | – | `by (cases t; simp)`, `qed auto` / `qed simp_all` for the cases left, `consider (a) A \| (b) B` then `proof cases` [read] |
| **Dafny** | yes | no | – | no [read] | the verifier; `match` in lemmas [recalled] |
| **OCaml** (5.5.1) | yes | yes; same names required | shared, must be equal [measured] | yes | – |
| **Haskell** (GHC 9.12.3) | yes, `(p; q)` | no ("may not bind any variables or constraints") [read; measured] | – | yes | – |
| **Rust** | yes | yes; same names required | shared, must unify exactly [read] | yes | – |
| **Swift** | yes (`case a, b:`) | yes; same names required | shared, "the same type" [read] | – | – |
| **Scala 3** | yes | no today; SIP-60 (accepted, not built) allows it | shared: the union of the types (`Int \| String`) [read] | yes | – |
| **Zig** | yes (`a, b =>`) | yes (capture) | per case, but only on a prong marked `inline` [read] | – | – |
| **Stitchwort today** | yes | no (`E-OR-PATTERN-BINDS`) | – (a catch-all's names are already per case) | yes | catch-all after a split; `cases then t` |

## 2. Findings

### 2.1 Lean 4: the body is copied, by a macro

Before elaboration, `expandMatchAlt` "expand[s] a match alternative such as
`| 0 | 1 => rhs` to an array containing `| 0 => rhs` and `| 1 => rhs`"
[read: `src/Lean/Elab/BindersUtil.lean`, lean4 `master` at `5ed6f4dc1a`].
The grammar puts the alternatives only at the top of an arm
(`sepBy1 (sepBy1 termParser ", ") " | "` in `matchAlt`,
`src/Lean/Parser/Term.lean`), so `some (.inl x | .inr x)` is a parse error
[measured]. The reference manual's "Pattern Matching" page gives the syntax
and says nothing about how the shared body is checked [read];
*Functional Programming in Lean* does: "Behind the scenes, the result
expression is simply duplicated across each pattern", "the variables bound
by the patterns are not required to have the same types", "only variables
shared in all patterns can be referred to in the result expression", and
"Because there is a potential for confusing behavior, it's a good idea to
be careful when using them" [read: FPIL, "Additional Conveniences",
"Or-Patterns"].

Measured, Lean 4.35.0 (§6, `l1`–`l4`):

- `| .inl x | .inr x => toString x` on `Sum Nat String` checks, and `#print`
  shows two arms. A proof with `same` at three types,
  `| .plus, same | .minus, same | .star, same => by subst same; rfl`, checks.
- **Names aren't checked.** `| .inl x | .inr y => "a"` is accepted, with
  two unused-variable warnings; `| .inl x | .inr y => x` fails with
  "Unknown identifier `x`" and no mention of the second alternative. FPIL
  shows the sharper trap: a name bound in one alternative and also defined
  globally silently means the global in the other alternative.
- **An error doesn't name its alternative.** `| .inl x | .inr x => x + 1`
  reports "failed to synthesize instance of type class `HAdd String Nat Nat`"
  at the body; the reader works out the alternative from `String`. In the
  proof `| .plus | .minus | .star => rfl` with only `star` false, the error
  is a type mismatch against `lvl Tok.star = 1`: the goal gives it away,
  the message doesn't say it.
- **An error in every alternative is printed once per alternative**, at the
  same position (two identical-looking `HAdd Nat String` errors). A hole
  `_` in a shared body reports twice, with `x : String` and `x : Nat`.
- Coverage and recursion see the copies: a repeated alternative is
  "Redundant alternative", a missing one is listed under "Missing cases",
  structural recursion through `| .inl _ :: xs | .inr _ :: xs => 1 + len xs`
  is accepted, and there is one equation lemma per alternative (`len.eq_2`,
  `len.eq_3`), as Stitchwort's `f.eqK.or1`, `.or2` already are.
- **A catch-all is checked once, not per case.** After `| .plus => by decide`,
  the arm `| _ => by decide` fails with "Expected type must not contain free
  variables: `lvl x✝ ≤ 2`"; the same proof as `| .plus | .minus | .star =>
  by decide` checks. So in Lean the or-pattern is the *only* term-level way
  to share a proof over cases; Stitchwort's catch-all already does more.

In tactic proofs the same sharing is `cases t <;> rfl`, `cases t` then
`all_goals …` or `case plus | minus | star => …`, and
`cases h with | inl h | inr h => simp [h]` (merged alternatives binding `h`
at two types) [all measured]; the manual defines `case tag₁ | tag₂ => tac`
as "equivalent to `(case tag₁ => tac); (case tag₂ => tac)`" [read by
SW-4219]. A failure there is better labelled than in term mode: the error
carries the goal's tag, `case star ⊢ lvl Tok.star = 1` [measured].

### 2.2 Rocq: the same, with the names checked

The manual allows it in two sentences: "Multiple patterns that share the
same right-hand-side can be factorized using the notation" `|`, and
"factorization of (not necessarily multiple) patterns that share the same
variables is possible"; "Nested disjunctive patterns are allowed, inside
parentheses" [read: Rocq 9.0 reference manual, "Extended pattern matching",
"Disjunctive patterns"]. It doesn't say what happens to types. Measured,
Rocq 9.1.1 (§6, `t1`–`t11`):

- `match x with inl a | inr a => existT (fun T => T) _ a end` on
  `nat + bool` checks and prints as two arms, `existT … nat a` and
  `existT … bool a`: the body is elaborated per alternative, the `_` solved
  differently in each. With a dependent return type, `inl a | inr a => a`
  checks at `match x with inl _ => nat | inr _ => bool end`.
- A tactic in the body runs per alternative:
  `match h with or_introl a | or_intror a => ltac:(auto) end` produces
  `f a` in one arm and `g a` in the other.
- Names are checked: `inl a | inr b` is "The components of this disjunctive
  pattern must bind the same variables (a is not bound in all patterns)".
- An error shows the context, which identifies the alternative by the
  name's type but doesn't name it: for `inl a | inr a => a + 1`, "In
  environment `x : nat + bool`, `a : bool`. The term "a" has type "bool"
  while it is expected to have type "nat"".
- A catch-all is checked per case, as in Stitchwort: `| _ => fun h => O_S _
  (eq_sym h)` after `Plus` prints as separate `Minus` and `Star` arms with
  different implicit arguments.

Tactics: `destruct t; reflexivity` reports "Unable to unify "1" with "lvl
Star"" for the one failing case; ssreflect's `by case: t.` on the same goal
says only "No applicable tactic" [measured]. Ltac's `;` applies the second
tactic "to all the goals produced by the prior application" [read by
SW-4219]; `destruct h as [h | h]; [right | left]; exact h` and ssreflect's
`case: h => [h|h]; [right|left]` name per-branch hypotheses with one name at
two types [measured]. Equations has no or-patterns; overlapping clauses
with a final catch-all are its way to share a right-hand side [recalled].

### 2.3 The other provers

- **F\*.** Desugaring checks "that the same variables are bound in each
  pattern" (error: "Patterns in this match are incoherent. Variable … is
  bound in some but not all patterns"), then `desugar_disjunctive_pattern`
  maps each alternative to a branch of its own with the same body [read:
  `src/tosyntax/FStarC.ToSyntax.ToSyntax.fst`, FStar `master` at
  `fc1776afe5`]. Whether the types may differ wasn't probed (the Nix
  package wanted a source build, which a paper lane doesn't run).
- **Agda** rejects `f (a | b) = a` (it reads `a | b` as an application:
  "The constructor a expects 0 arguments") and **Idris 2** rejects
  `f (A x | B x) = x` ("with application not implemented yet") [measured].
  In both, a catch-all clause is the sharing tool, and in Agda its body is
  checked once against the unrefined type [recalled].
- **Isabelle/Isar.** `case` invokes one named context: "`case a: (c x₁ … xₘ)`
  invokes a named local context" [read: Isar reference manual, 24 Oct 2026,
  §6.5]; there is no `case (A | B)`. Sharing is by method: "Structural
  composition `m₁; m₂` means that method `m₁` is applied with restriction to
  the first subgoal, then `m₂` is applied consecutively with restriction to
  each subgoal that has newly emerged" (§6.4.1), and a terminal "`qed m₂`
  refines any remaining goals by proof method `m₂`" (§6.4.2), so the idiom
  is to write out the interesting cases and close the rest with
  `qed auto`. `consider (a) A | (b) B | (c) C` states a case split of one's
  own and `proof cases` walks it, one `case` per branch (§1.5.3).
- **Dafny.** "Disjunctive patterns may not bind variables, and may not be
  nested inside other patterns" [read: Dafny reference, "Case and Extended
  Patterns"].

### 2.4 Programming languages: one type, or no binding

- **OCaml**: "The two sub-patterns … must bind exactly the same identifiers
  to values having the same types" [read: manual 5.3, "Patterns"].
  Measured: `L a | R a` on `(int, string) sum` is "The variable a on the
  left-hand side of this or-pattern has type int but on the right-hand side
  it has type string"; different names is "Variable a must occur on both
  sides of this | pattern". With a GADT, the type equations of the
  alternatives are *not* available in the body: `| I | B -> x + 1` fails
  with "x has type a but an expression was expected of type int", where
  `| I -> x + 1` alone checks. This is the cost of checking the body once:
  whatever the alternatives learn separately is lost.
- **Rust**: ill-formed if "the same set of bindings are not introduced in
  `p` and `q`, or the type of any two bindings with the same name in `p`
  and `q` do not unify with respect to types or binding modes" [read: Rust
  reference, `patterns.constraints.pattern`].
- **Swift**: "all of the patterns must contain the same constant or
  variable bindings, and each bound variable or constant must have the same
  type in all of the case's patterns" [read: *The Swift Programming
  Language*, Statements].
- **Haskell**: or-patterns arrived in GHC 9.12 as `(p; q)` and "may not
  bind any variables or constraints", so no GADT evidence either [read:
  GHC user's guide, `OrPatterns`]. Measured, GHC 9.12.3: `g (A x; B x) = x`
  is "An or-pattern may not bind term or type variables such as 'x'", and
  `f (A _; B _) = 1` checks.
- **Scala 3**: alternatives "may not bind variables other than wildcards"
  today. SIP-60, accepted but not implemented, lifts that with a third
  rule: one body, and the name's type is the union, `x: Int | String`
  [read: SIP-60]. That needs union types, which Stitchwort doesn't have,
  and a union of `text = "&&"` and `text = "∧"` would be no use to
  `rewrite`.
- **Zig** is the one programming language with per-case checking, and it
  makes you ask for it: "Switch prongs can be marked as `inline` to
  generate the prong's body for each possible value it could have", and
  `inline else => |slice| slice.len` works over payloads of four different
  types [read: Zig 0.13 language reference, "Inline Switch Prongs"].

### 2.5 What the pattern is

Three rules exist for a name bound in several alternatives:

1. **One type** (OCaml, Rust, Swift). Simple to explain; the body means one
   thing. It cannot express the motivating proofs: `text = "&&"` and
   `text = "∧"` are different types with no common one, and OCaml shows
   that even without bindings a once-checked body can't use what each
   alternative learned.
2. **A union type** (Scala's SIP-60). Needs unions.
3. **Per alternative** (Lean 4, Rocq, F\* by its desugaring, Zig's
   `inline`). The body is a template checked at each use. Every language
   whose `match` has to refine types per case chose this one, and none of
   them needed a kernel feature for it: the or-pattern is gone before the
   kernel sees the term.

Dependent types force the choice. Once each alternative refines the goal
and the hypotheses differently, even a body that binds nothing must be
checked per alternative (Stitchwort does this today), and then giving the
bound names their per-alternative types is the consistent rule, not an
extra. Stitchwort is in fact already past this point: a catch-all's names
are typed per case today (`| other, same => rewrite same`, the note's p2).

## 3. Risks seen elsewhere, and how Design 2 stands

| Pitfall (where seen) | Design 2 as written | Verdict |
|---|---|---|
| Alternatives binding different names accepted; a missing name falls through to a global (Lean) | every alternative must bind the same names; `E-OR-PATTERN-BINDS` reworded | covered, as Rocq, OCaml, Rust, F\* |
| An error doesn't say which alternative (Lean; Rocq shows only the context) | "an error in the body names its alternative", listed under Design 1 | must ship *with* binding, not after: see §4 |
| The same error printed once per alternative (Lean) | not addressed | amendment, §4 |
| A hole or hover shows one alternative's types (Lean prints one message per copy) | hover shows each type; the goal display follows `catch-all-goals.md` | covered; a hole in a shared body should list the alternatives' goals in one message |
| The body resolves differently per alternative: an overload, an instance, a method (`toString x` in Lean; `ltac:(auto)` in Rocq) | "harmless, since the body is already elaborated per row" | true for soundness; a reader's surprise in programs. Accept, and say it in the guide: §4 |
| Elaboration cost: the body is checked once per alternative, and alternatives in several columns multiply | "unchanged: the same leaves are checked as with the arms written out" | agreed; the cost is hidden by the notation, not created by it |
| Coverage, redundancy, termination, equations (Lean: all per alternative) | rows per alternative already | no issue found |
| No nesting (Lean, Dafny) | nested allowed, as today | better, as Rocq and OCaml |
| A catch-all checked once (Lean, Agda) | checked per case already | Stitchwort and Rocq agree |

## 4. Recommendation

**Confirm Design 2** (or-patterns that bind, each alternative checked on
its own), with Design 1 as the note has it. Reasons:

- It is the established rule in the provers that have or-patterns at all:
  Lean 4 and Rocq both ship it today, in term mode, with dependent types
  [measured]. Design 2 is Rocq's rule (same names required, nesting allowed,
  per-alternative types).
- The one-type rule of Rust and OCaml can't state the proofs that motivate
  this, and Stitchwort has no line between proofs and programs on which to
  apply one rule to each.
- Every program legal under a one-type rule means the same under Design 2:
  it accepts more and changes nothing. A newcomer from Rust is surprised
  only by something being allowed.
- A tactic-style combinator is not a better fit. Lean, Rocq and Isabelle
  reach for `<;>`, `;` and `qed auto` because their proofs are scripts over
  a list of goals; Stitchwort's proofs are terms, where the arm *is* the
  goal, and the catch-all after a split already is `<;>` over the remaining
  cases (with Rocq's per-case checking, which Lean's term mode lacks). A
  combinator would be a second way to say what the arm says. The note's
  Design 3 stays "not now"; see the finding in §7 about the one gap.

**Amendments to Design 2:**

1. **The alternative-naming note is part of the feature.** An error in a
   shared body says which alternative it is in and the bound names' types
   there ("in the alternative `Inl (Inr same)`, where `same` is
   `text = "∧"`"). This is the confusion Lean's users are warned about and
   the answer to "what can I do in the body": the error teaches it. It
   ships in the same lane as binding.
2. **One error when every alternative fails the same way.** If the body
   fails in all alternatives with the same code at the same span, report it
   once ("in each of the 3 alternatives"), not once per alternative.
3. **Say the rule in user words, in the guide and `docs/syntax.md`:** "an
   arm with several alternatives is checked as if its body were written
   under each one; a name may have a different type in each, and the body
   must make sense for all of them". Include the program example and the
   failing one from "In plain words", and note that a method call or
   overloaded name in the body resolves per alternative.
4. **A hole in a shared body lists every alternative's goal** in one
   message, as the catch-all's "checked in N cases" note does, rather than
   showing the last.

No change to the kernel, to terms or to hashes, as the note says.

## 5. D3694 restated

**D3694: let or-patterns bind names, each alternative checked on its own,
as Lean 4 and Rocq do? [rec: yes]**

- **The problem.** A proof that does the same thing in several cases must
  be written once per case whenever the cases name a fact: `andLevels` is
  four arms for two proofs, `spellsOfTests` 30 for four. About 107 repeated
  arms in `tools/fmt` and 150 in std can't be joined by anything written
  today [measured by SW-4219, heuristic].
- **The change.** Allow `| Inl same | Inr same => body` when every
  alternative binds the same names. The body is checked as if written
  under each alternative, so a name may have a different type in each;
  the body must make sense for all of them. An error says which
  alternative it is in and what the names' types are there. This is what
  Lean 4 and Rocq do [measured]; Rust, OCaml and Swift instead require one
  type, which can't express these proofs.
- **What it should do.** Those arms written once; with Design 1 (no
  decision needed), up to 2.6% of `tools/fmt`'s theorem lines and 2.4% of
  std's go [measured by SW-4219, an upper bound]. In programs, an
  or-pattern may now bind (`| Circle r | Dot r => …`), with the same rule.
  No kernel, term or hash change. About 2 to 2.5 hours of Opus, including
  the error note and the guide [estimated, from the note's figure plus the
  amendments].

## 6. Probes

Run 19 November 2026 through `nix shell nixpkgs#…`: Lean 4.35.0, Rocq 9.1.1
(`nixpkgs#coq`), OCaml 5.5.1, Agda 2.8.0, Idris 2 0.8.0, GHC 9.12.3. Files were in the
lane's scratchpad (`sw4228/p/`); the texts that carry a claim:

```lean
-- l1: accepted; #print shows two arms
def show1 : Sum Nat String → String
  | .inl x | .inr x => toString x
-- l1: accepted with unused-variable warnings only
def bad1 : Sum Nat String → String
  | .inl x | .inr y => "a"
-- l1: "failed to synthesize instance of type class HAdd String Nat Nat"
def bad2 : Sum Nat String → Nat
  | .inl x | .inr x => x + 1
-- l1: accepted
theorem len1 (t : Tok) (s : String) (h : s = spell t) : s.length = 1 :=
  match t, h with
  | .plus, same | .minus, same | .star, same => by subst same; rfl
-- l2: "unexpected token '|'; expected ')', ',' or ':'"
def nest : Option (Sum Nat Nat) → Nat
  | some (.inl x | .inr x) => x
  | none => 0
-- l3: "Expected type must not contain free variables  lvl x✝ ≤ 2"
theorem c1 (t : Tok) : lvl t ≤ 2 :=
  match t with
  | .plus => by decide
  | _ => by decide
-- l4: the HAdd error twice, at the same position
def w : Sum Nat Nat → Nat
  | .inl x | .inr x => x + "a"
```

```coq
(* t2: accepted; prints as two arms, nat and bool *)
Definition a4 (x : nat + bool) : {T : Type & T} :=
  match x with inl a | inr a => existT (fun T => T) _ a end.
(* t3: "must bind the same variables (a is not bound in all patterns)" *)
Definition a3 (x : nat + nat) : nat := match x with inl a | inr b => 0 end.
(* t8: "In environment x : nat + bool, a : bool. The term "a" has type "bool" ..." *)
Definition a6 (x : nat + bool) : nat := match x with inl a | inr a => a + 1 end.
(* t10: prints as  or_introl a => f a | or_intror a => g a *)
Lemma e2 (p q r : Prop) (h : p \/ q) (f : p -> r) (g : q -> r) : r.
Proof. exact (match h with or_introl a | or_intror a => ltac:(auto) end). Qed.
```

```ocaml
(* o2: "The variable a on the left-hand side of this or-pattern has type
   int but on the right-hand side it has type string" *)
let a2 (x : (int, string) sum) = match x with L a | R a -> ()
(* o4: "The value x has type a but an expression was expected of type int" *)
type _ t = I : int t | B : bool t
let g4 : type a. a t -> a -> int = fun t x -> match t with
  | I | B -> x + 1
```

Not probed: F\* (source build), Dafny,
Isabelle, Scala, Swift, Rust, Zig (manuals read instead). Stitchwort's own
behaviour is quoted from the note's probes, not re-run.

## 7. Findings

- **A `match` whose arms are all alike still needs one constructor named**
  (`match tok with | _ => byComputing` doesn't split, the note's p1), where
  Lean, Rocq and Isabelle each have a two-word idiom (`cases t <;> tac`,
  `destruct t; tac`, `by (cases t; simp)`). With Design 2 the gap is one
  arbitrary constructor name per such proof (607 repeats in `tools/fmt` are
  in all-alike groups). If lanes still write these out after Design 1 and
  2, the note's Design 3b (a targeted `cases x then t`) is the form with
  the most precedent. Not part of D3694.
- **`docs/syntax.md` says "An alternative can't bind a variable … as in
  Scala"**: Scala has accepted SIP-60 to lift that, so the comparison will
  date whatever D3694 decides.
- **The note's Rocq and Lean precedents marked [recalled] are now
  measured**, and one was understated: Rocq doesn't only require "the same
  variables", it types them per alternative.

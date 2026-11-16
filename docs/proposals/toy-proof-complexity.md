# Why is the toy proof 16 times its program?

Fable paper lane, SW-3500 (D3627), 16 November 2026. No builds or tests
were run and no code was changed. Every number is marked **[measured]**
(counted here with `grep` and short scripts over `tools/toyfmt/src`, or
quoted from [after-the-toy-proof.md](after-the-toy-proof.md)),
**[cited]** (from a paper or project page fetched for this note; sources
at the end) or **[estimated]** (mine; nothing was tried). The estimates
for Lean and Rocq are the weakest part of this note, which is why §5
proposes measuring one.

Matt's question: the proof of the toy formatter looks an order of
magnitude more complicated than the program. Is that the task, our
approach, or Stitchwort?

## In plain words

**The short answer.** All three, in roughly these shares [estimated]:

| Cause | Share of the 27,349 lines | As a multiple of the program |
|---|---|---|
| The task itself: what any proof assistant would also need | about a quarter (20-35%) | 3 to 6 times |
| Our approach: dead ends kept, the same walk done three times, facts recovered from printed text that the program could have carried | about a quarter (20-30%) | 3 to 4 times |
| Stitchwort: proofs are written out as terms, with no simplifier and no short way to build or take apart "there is an x such that A and B and C" | about half (40-50%) | 6 to 8 times |

**Is 16 times unusual?** No, but it is at the heavy end. Published
ratios for functional programs proved in Coq, HOL4 or Lean run from 3
to 10 times (CompCert about 6, a Lean proof about a pretty-printer 9, a
verified lexer 10); seL4, C code proved in Isabelle, is about 20 [all
cited, §1]. The toy sits between the two groups, and nobody else's
figure counts dead lemmas and doc comments as ours does.

**Is the approach unusual?** No. The toy already uses the three best tricks we found in the literature: the
printer's line breaks are "just white space" whatever the width
(Danielsson), a grammar written as a relation that the parser is proved
against one way and the printer the other (Narcissus), and "these two
tokens may stand next to each other" as a table (ZipLex). **We found no
published, machine-checked formatter that does what the toy does**:
comments, a width-driven layout, an indentation-sensitive grammar, a
parser that is actually run, and idempotence. The nearest each do one
or two of those. So there was no small known proof that we missed, but
there are two patterns we use by hand that others get from a library
(§4.2).

**What Lean or Rocq would change.** The same theorem about the same
program would be about 5,000 to 10,000 lines in idiomatic Lean 4, 3 to 6
times the program [estimated, low confidence], and a little more in
Rocq. The saving is not cleverness: it is a simplifier that discharges
the hundreds of "unfold this, rewrite that, both sides now agree"
lemmas, and angle brackets for building and taking apart nested
"exists/and" facts, which the toy does by hand 4,157 times [measured].
The two nearest published proofs (the Lean printer and the lexer above)
are at 9 and 10 times with that kind of help, so my Lean figure may be
too kind; §5 proposes measuring it.

**So is the complexity justified?** The part that is the task is
justified and is where the three bugs were found. The rest is a fair
measurement of two things we can fix: Stitchwort's proof language is
still a *checker's* language (every step written out), and the first
proof of anything carries its scaffolding. Neither says the design is
wrong. Both say: before proving something five times larger, build the
simplifier and the "exists/and" syntax, and use the two or three known
patterns in §4.2.

## 1. Published proof-to-code ratios

All **[cited]**: each figure was read from the paper or page named, by
a research agent that downloaded it for this lane and quoted the
sentence; the ratios are arithmetic on those figures unless the source
states one. Two rows are our own `wc -l` of a public repository and
say so. Links are in "Sources".

| System (prover) | What is counted | Figures | Proof to code |
|---|---|---|---|
| **seL4** (Isabelle), SOSP 2009 | C and assembler against Isabelle proof script, "including framework, libraries, and generated proofs" | 8,700 C + 600 asm; 200,000 proof | about 20:1 (Heiser's blog states "over 20 lines of proof per line of C") |
| seL4, TOCS 2014 | the same code against all proofs *and specifications*, with the later security and binary proofs | about 10,000; 480,000 | about 48:1 |
| seL4, effort | person-years | kernel 2.2; proof 20 (11 specific to seL4, 9 on tools and libraries) | 9:1 in effort |
| **CompCert back-end** (Coq), JAR 2009 | non-blank, non-comment lines, split by kind | code 14%, semantics 10%, statements 21%, proof scripts 44%, directives 8% of 37,570 | the paper says "about 6 times larger than the program"; proof scripts alone 3.1:1; statements and scripts 4.6:1 |
| CompCert, CACM 2009 | Coq without comments and blanks | 42,000: 14% algorithms, 10% semantics, 76% proof | 5.4:1 |
| **CakeML** back-end (HOL4), ICFP 2016 | proof scripts, whole development | about 100,000 | no code size published |
| CakeML's parser (HOL4): **our count of the repository, not published** | `wc -l` with blanks and comments | PEG definition 850; soundness 1,424; completeness 3,623; grammar properties 848 | about 7:1; completeness alone 4.3:1 |
| **Validated LR(1) parsers** (Coq), ESOP 2012 | Coq without comments | 2,500 in all; two validators about 200 each; proofs 200 + 500 + 700 | 3.5:1; against "over 20 000 lines" for a verified parser *generator* (Barthwal and Norrish), which the paper gives as the reason to validate |
| **TRX**, a verified PEG interpreter (Coq) | proofs and their Ltac against definitions | stated as a ratio | "roughly 4-5x … so low thanks to heavy use of Ltac automation" |
| CoStar, verified ALL(*) parser (Coq), PLDI 2021 | "specification" (which includes the parser) and proof | 5,000 + 5,000 | 1:1 |
| Vermillion, verified LL(1) generator (Coq), ITP 2019 | definitions and proofs together | about 8,000 | no split |
| **Narcissus** (Coq), ICFP 2019 | what a user writes per binary format | 10-20 lines of format, 10-20 of declarations | no hand proof per format: the decoder and its proof are derived by tactics |
| **EverParse / LowParse** (F\*), USENIX Security 2019 | combinator library; per-format input and generated F\* | LowParse 32,210 lines of F\*; TLS: 1,601 lines of format description give 69,534 generated | no hand proof per format |
| "A Pretty Expressive Printer" (Lean), OOPSLA 2023: **our count of the artifact, not published** | `wc -l` of its Lean files; the definitions are a model of the printer, the shipped printers are separate OCaml and Racket | definitions 408; claims 1,697; supporting lemmas 1,962 | about 9:1 |
| **ZipLex**, a verified invertible lexer (Scala/Stainless, SMT-automated), 2025 | proof code against implementation | stated as a ratio | "roughly ten times more lines" |
| Verbatim, a verified lexer generator (Coq), 2021 | specification and proof | 700 + 1,200 | no code split |
| IronFleet (Dafny, SMT-automated), SOSP 2015 | spec, implementation, proof annotation | 1,400; 5,114; 39,253 | "3.6 to 1" at the implementation layer (stated); 7.7:1 overall |
| Verdi (Coq), PLDI 2015 | lines with blanks and comments | Raft's linearizability: 520 code, 4,144 proof; a key-value store: 138, 337 | 8:1; 2.4:1 |
| Verdi's full Raft proof (Coq), CPP 2016 | code against proof, framework excluded | 530; 50,000 | 94:1 |
| CertiKOS mC2 (Coq), OSDI 2016 | C and assembly against auxiliary definitions and proof scripts | 6,500; about 40,000 + 50,000 | about 14:1 |
| Coq 8.1's standard library and the Isabelle AFP, from the "QED at Large" survey | shares of lines | statements 11% / 19%, definitions 8% / 8%, proofs 53% / 58% | about 7:1 proof to definitions |
| **The toy** (Stitchwort) | program against proof files; and by kind (§3.1) [measured] | 1,679; 27,349 (bodies 17,302, statements 4,470, proof-only definitions 2,127) | 16:1; bodies alone 10:1 |

Not found: a framework size for Narcissus; any published size for
CakeML's parser or printer; a size for Danielsson's Agda development;
and **no verified source-code formatter with a reported size at all**
(next section).

**Reading the table.**

- Purely functional programs proved in the language they are written
  in, with the provers' ordinary automation, sit between **3:1 and 10:1**:
  CompCert, the LR(1) validator, TRX, CakeML's parser, Verdi's small
  systems, the pretty expressive printer; ZipLex's lexer, with an SMT
  solver doing the routine steps, is at 10:1.
- **14:1 to 20:1 and up** belongs to C code proved by refinement
  (CertiKOS, seL4) or to a property much deeper than the code (Raft,
  94:1: there the proof's size follows the property, not the code).
- **The toy at 16:1** (10:1 on proof bodies) is above every functional
  comparator and below seL4. It proves a deep-ish property (a round trip
  through a layout engine, a lexer and an indentation-sensitive parser)
  of a small program, with almost no automation. Both halves of that
  sentence push the ratio up; the table can't separate them, which is
  what §3 and §5 are for.
- Counting changes a ratio as much as the system does: seL4 is 20:1 or
  48:1 by what is included, CompCert 3:1 or 6:1. The toy's 16:1 counts
  doc comments, proof-only definitions and 2,000 dead lines.
- The two closest comparators are informative in opposite directions.
  *CakeML's parser:* completeness of a parser against its grammar costs
  4.3 times the parser in HOL4; the toy's read-back layer, the same kind
  of theorem with indentation and comments added, is 4,753 lines for a
  505-line parser, 9.4 times [measured]. *The pretty expressive
  printer:* a Lean proof about a layout engine at 9:1. That is a warning
  against my own Lean estimates in §3: Lean's automation did not make
  that proof small. (Its theorem is harder than ours in one way: it
  proves the layout chosen is *optimal*, which the toy never needs,
  since any layout re-parses.)

## 2. The literature on verified parsers, printers and round trips

All **[cited]**: read from the paper or repository named, fetched for
this lane, except where a line says "not checked". "Mechanised" means
checked by a proof assistant.

| Work | What is proved | The trick that keeps it small | Layout choice, indentation, comments | Size |
|---|---|---|---|---|
| **Danielsson**, "Correct-by-construction pretty-printing" (Agda, 2013) | "if a given value is pretty-printed, and the resulting string parsed (with respect to the same, unambiguous grammar), then the original value is obtained". It proves the string is *in the grammar* for that value; no parser is run | A document's type names the grammar and the value it prints (`Doc g x`), so a rule that prints the wrong thing doesn't type-check. The renderer is proved once. A line break's grammar is "white space", so the width can't change what is parsed | Groups, nesting and width: yes (Wadler's renderer; "No guarantees are made about 'prettiness'"). Indentation-sensitive grammar: no. Comments: no | not stated |
| **Rendel and Ostermann**, invertible syntax descriptions (Haskell, 2010) | Nothing mechanised, and no round-trip theorem is stated; hand-written isomorphisms are unchecked ("it is not checked that the two directions are really inverse") | One description runs as a parser or as a printer | White space as allowed, wanted or required; no width, no comments | a library |
| **Narcissus** (Coq, 2019) | "Given a correct decoder … and correct encoder … for a common format …, decode is an inverse for encode" | The format is a *relation*. Encoder and decoder are each proved against it by a lemma per combinator and tactics; the round trip follows once, for all formats. The decoder inverts the whole relation, so the encoder's free choices need no reasoning | Binary formats only | 10-20 lines per format; no proof by hand |
| **EverParse / LowParse** (F\*, 2019) | "parsing is the inverse of serialization", and non-malleability | A serialiser's type names its parser; "For each specification combinator, we prove non-malleability and inverse properties … All properties are verified by typing the library" | Binary | LowParse 32,210 lines, once |
| **Biparsers**, Xia et al. (Haskell, main theorems in Coq, 2019) | Round-tripping composes: "only the individual atomic components need round-tripping proofs" | A proof per primitive, none per program | none | not stated |
| Sleurink, MSc thesis (Isabelle, 2024) | A parser-and-printer combinator library with a well-formedness rule per combinator | As above | not checked | not checked |
| **Jourdan, Pottier, Leroy**, validated LR(1) parsers (Coq, 2012) | A verified *checker* confirms that an untrusted parser table agrees with the grammar (sound, complete, unambiguous) | Validate, don't verify: 2,500 lines against "over 20 000" for a verified generator | no printing | 2,500 |
| **CakeML** (HOL4) | Its PEG parser is sound and complete for its grammar. Its source printer is *unverified* ("Printing code is added in two unverified passes"). A round trip exists for s-expressions only: `fromString (sexp_to_string x) = SOME x` | A grammar in the middle; completeness proved once against it | no | parser proofs about 5,900 lines (our count, §1); the s-expression file 712 |
| **ZipLex**, Chassot and Kunčak (Scala/Stainless, 2025) | A lexer and its inverse: `lex(print(ts)) = ts` for any token list that is *separable*, and `print(lex(s)) = s` | Separability as a predicate on neighbouring tokens, proved once against longest-match lexing | lexing only | proof "roughly ten times more lines" than the implementation |
| **Verbatim** (Coq, 2021) | A lexer generator's longest-match rule | | lexing only, no printing | 700 specification + 1,200 proof |
| **Menhir's unparsing**, Pottier (2024, not mechanised) | Explicitly *not* a round trip: "we cannot guarantee an end-to-end round-trip property of the form parse(unparse(t)) = t". Only the bracket-insertion step is guaranteed; spacing between tokens is left to the user, and comments are future work | | no | |
| **Quotient lenses**, Foster et al. (2008, paper proofs) | Lens laws up to an equivalence, with "canonizers" at the edges to absorb white space | Say "the same up to white space" once, at the edge | white space as an equivalence | |
| **FliPpr**, Matsuda and Wang (2013, not mechanised) | A parser is *derived* from a pretty-printer written with Wadler's combinators | Program inversion; "lines are interpreted as whitespaces" | layout: yes; comments: not checked | |
| **BiYacc** (not mechanised) | `parse (print s t) = t` and `print s (parse s) = s`, "guaranteed by construction" | The only one here with comments: "We store layout information following each terminal in an additional field in the CST … and treat comments in the same way". It keeps the source's layout; it doesn't reformat | comments: yes; layout choice: no | |
| **Wadler; Bernardy** printers | Algebraic laws, on paper ("program calculation") | | | not mechanised, as far as one search found |
| **Porncharoenwase, Pombrio, Torlak**, "A pretty expressive printer" (Lean, 2023) | The layout chosen is valid and *optimal* for a cost function. Nothing about tokens or parsing | | layout: yes | 4,157 lines of Lean (our count) |
| CompCert's printers | Unverified: "For phase 4 (assembly and linking), we have no formal guarantees yet" (the manual) | | | |
| Adams, indentation-sensitive grammars (POPL 2013) | A grammar formalism for the offside rule; we found no mechanised proof about any indentation-sensitive parser | | indentation: yes | |

**What this says about the toy.**

1. *There was no small proof to copy.* Three searches for a verified
   source-code formatter found none. The printers of the two flagship
   verified compilers are unverified. The closest tool author (Pottier,
   2024) says in print that he can't guarantee the round trip.
2. *The toy's architecture is the literature's.* A relation in the
   middle (`Spelled`, as Narcissus and CakeML have a format or grammar
   in the middle); line breaks that mean only white space whatever the
   width (the engine's "any reading", Danielsson's `line`); a pairwise
   "may follow" for tokens (`Joins`/`Stands`, ZipLex's separability);
   comments stored on tokens (BiYacc).
3. *What the others have that we don't is a library that carries the
   proof.* Narcissus, LowParse, biparsers and Danielsson each prove the
   round trip once per **combinator**; a user who writes a format with
   the combinators proves nothing. The toy proves it once per
   **construct of Sprig**, by hand, twice (read-back and spelling:
   9,539 lines, a third of the proof [measured]).
4. *Every published size we found is for something simpler,* and the
   ratios aren't small: a lexer alone at 10 times in an SMT-automated
   tool, a layout engine alone at 9 times in Lean, parser completeness
   alone at 4 times in HOL4. The toy does all three at once with
   indentation and comments, at 16.

## 3. The toy proof in Lean 4 and in Rocq, layer by layer

### 3.1 What the toy's proof text is made of

Before comparing, what the 27,349 lines are [measured, by a script that
splits each proof file at `theorem`, `def` and `--|`]:

| Kind of line | Lines | Share |
|---|---|---|
| Proof bodies (after the `:=`) | 17,302 | 63% |
| Theorem statements (1,261 found by the script) | 4,470 | 16% |
| Definitions used only by the proofs (375 `def`s: `Spelled`, `Events`, `Joins`, `StepsTo`, …) | 2,127 | 8% |
| Doc comments | 1,984 | 7% |
| Blank lines, imports, the rest | about 1,470 | 5% |

So the *proofs* are about 10 times the program, and saying what is to be
proved (statements and their definitions) is another 4 times. Other
measurements that matter for the comparison:

- **The ratio isn't a formatting effect.** Counting characters that
  aren't white space gives 19 times, and counting tokens 18 times
  [measured, with a slightly different split of files]. One argument per
  line makes the proofs tall, but they are as dense as the program.
- **`Witness` and `Both`** (the constructors of "there is" and "and")
  are written 4,157 times: 1,033 and 3,124. `rewrite` 906 times, `rfl`
  1,989, `omega` 323, `cases` 75.
- **Arguments written as `_`:** 1,774. One theorem of the 1,262 uses
  implicit parameters (`plainLexemeReads`), though the proving guide asks
  for them (D2422).
- **Half the proofs are short:** the median body is 5 lines; 475 bodies
  are 3 lines or fewer. At the other end, 59 bodies of 50 lines or more
  hold 7,680 lines, 44% of all proof-body lines.

Std's parser-proof library (`Parse.Reads`, `Runs`, `Paced`, `Among`:
some 350 theorems, per parse-proof-library.md §0) is *not* in the 27,349.
Lean and Rocq have no equivalent that fits, so a port would have to write
one; the estimates below leave it out on both sides.

### 3.2 What Stitchwort has and doesn't

From `docs/proving-guide.md` §3 and `docs/syntax.md`: a proof is a term.
The closers are `rfl`, `omega`, `ring`, `byDecision`, `Finite.check` and
`cases` (splits what the *goal* is stuck on, 64 cases at most);
`rewrite … in`, `calc`, and `match` do the steering; induction is
recursion. There is a proof search at a `?` (`stitchwort goal`), which
writes a term. There is no simplifier (`simp` is stage 3 of
[proof-automation.md](proof-automation.md), deferred), no way to split a
hypothesis except `match`, no anonymous constructor, no "do the same in
every case", no lemma sets applied by the shape of the goal, and no
tactic that walks a program applying a registered lemma per operation.

What Lean 4 has that bears on this proof (core Lean, without Mathlib,
unless noted):

| Lean 4 | What it does here |
|---|---|
| `simp`, `simp_all`, `@[simp]` lemma sets, equation lemmas made for every definition | "unfold, rewrite with the obvious lemmas, close by computation", in one word. The toy's 906 `rewrite`s and most `f.eqN` uses |
| `⟨a, b, c⟩`, `obtain ⟨x, h1, h2⟩ := h`, `rcases`, `refine ⟨_, _, ?_⟩` | builds and takes apart nested "exists/and" without naming a constructor: the 4,157 `Witness`/`Both` |
| a `structure` in `Prop` with named fields | a five-part conjunction read as `h.offsets`, not by position |
| `cases h`, `induction … with`, `<;>`, `all_goals`, `case _ | _ =>` | split a hypothesis; one script for many cases |
| `omega`, `decide` | as Stitchwort's `omega`, `byDecision` |
| `grind` (since v4.22 [cited: Lean release notes]) and `aesop` (a separate package) | backward and forward chaining through a lemma set: "every parser function keeps P" |
| `Std.Do` and `mvcgen` (since v4.22 [cited: Lean release notes]) | walks a monadic program and leaves only the side conditions: the walks, perhaps the rule triples |
| implicit arguments by default | no `_` arguments |

Rocq has the same kinds of thing under other names: `simpl`, `cbn`,
`rewrite … in *`, `autorewrite` with hint databases, `destruct h as (x &
h1 & h2)`, `inversion`, `lia`, `eauto` with hint databases, `;` to run
one script on every case, the Equations plugin for functions with their
own induction principles, and Ltac for a project's own tactics (the
CompCert and Software Foundations style is a few project tactics that
finish most routine goals).

### 3.3 Layer by layer

"Lean" means: the same program ported function for function, the same
final theorems, the same layers, written as a careful Lean user would,
with dead lemmas already gone. Lines are proof-file lines, statements
and definitions included. All Lean and Rocq figures **[estimated]**.

| Layer | Toy: theorems, lines [measured] | What automation collapses | What stays: the task's content | Lean 4 lines | Confidence |
|---|---|---|---|---|---|
| **Engine**: any way a document may print | 246, 4,089 (53 theorems dead) | Each invariant (`Uniform`, `Joins`, `Lays`, words) is one induction over the steps, with a 26-arm `match` whose arms are mostly "rewrite the step, apply the operation's lemma". In Lean: `induction … <;> simp_all [step]` with the hard arms by hand | Defining "a reading" (what the printer may do whatever the width), proving the real printer is one, and saying what each invariant *is*. The `fits` and comment-waiting cases (where bug 3 was) | 800-1,500 | medium |
| **Lexer**: printed pieces lex back | 153, 2,277 | Character classes: "this character is none of these ten" is `decide` or `simp`; per-lexeme lemmas mostly `simp` with `omega` | "Tokens don't merge" (which neighbours need a space) and the comment-to-end-of-line rule. Lean's `String` is harder to reason about than a list of characters, so a port would lex lists | 500-1,000 | medium |
| **Rules**: what each rule prints, and where | 399, 7,416 (83 dead) | Rule triples compose by the shape of the rule's document, so a lemma set (`aesop`, `grind`, or 30 lines of project tactic) proves most of the 46 rule lemmas from the rule's definition. Words, joins and events are three passes over the same rules; one statement could carry all three | Stating what each construct prints (`Events`): this is the style's specification. Whether the nested "exists" inside `Events` resist automation I can't tell without trying | 1,200-2,500 | low |
| **Walks**: what the parser guarantees | 201, 3,800 | Nearly all of it. One Hoare-style statement per parser function, proved by walking the function (`mvcgen`, or `simp` with the combinator lemmas); three predicates as one conjunction. Or none at all, if the parser returns values that carry their facts | The three predicates themselves (`Shaped`, `Lexical`, `Headed`) and the handful of functions with a real argument (operators, block ends) | 300-800 | medium-high |
| **Read-back**: the parser reads what spells a tree | 135, 4,753 | The plumbing of each case: unfold the parser on the tokens, discharge column side conditions by `omega`. `declines` lemmas by `simp` | An induction over the tree with one real case per construct: precedence, where a block ends, why an alternative isn't taken. This is completeness of a hand-written parser against a grammar; nobody gets it free | 1,200-2,500 | low |
| **Spelling**: printed tokens with positions spell the tree | 113, 4,786 | Most of the bulk. `exprSpells` is 1,010 lines; its three leaf cases are the same 28 lines three times, and its `Bracketed` case is mostly a nine-deep `Witness`/`Both` being opened and a seven-deep one being built. With `obtain`, `refine ⟨…⟩` and `all_goals` I'd expect a quarter to a third of the size | Matching the trace of what was printed against the grammar relation, case by case; comments landing on the same token | 1,000-2,000 | low |
| **Glue** | 15, 228 | Little | The final theorems, which are already short (`formatIdempotent` is 3 lines) | 100-200 | high |
| **All** | 1,262, 27,349 | | | **about 5,000-10,000** | low |

That is 3 to 6 times the program for Lean. For Rocq I'd put the same
proof at 6,000 to 12,000 lines in the ordinary style and near Lean's
figure with a few project tactics [estimated]; the differences between
the two are smaller than my error bars.

**Where Lean would be worse than Stitchwort, or no better.** Honesty
needs this list too:

- *No parser-proof library.* Lean's `Std.Internal.Parsec` has no lemmas
  to speak of; Stitchwort's `Parse.Reads` and `Runs` are a real asset.
  A port writes its own first.
- *Strings.* Reasoning about Lean's `String` is unpleasant; ports work on
  `List Char`.
- *The mutual induction over a tree with lists in it.* Lean's nested and
  mutual structural recursion is workable but not smooth; the toy's
  1,400-line mutual induction went through "with no type error"
  (friction 86), which a Lean user would envy.
- *`simp` is not free.* Proofs that lean on it break when a lemma set
  changes, are slow to check, and hide what was used. A term checks fast
  and never changes meaning. For proofs written and maintained by
  agents, the right balance may be different from a human's: an agent
  doesn't mind writing 30 lines, but it does pay for them in context,
  and Matt pays when he reads them.
- *The hard thinking is the same.* Finding `Reads` (the engine's "any
  reading"), `Spelled`, the edge and `follows` design for token joins,
  and the top-down sketch that made estimates hold: none of that is
  cheaper in Lean. By the NOTES' own account that is where the lanes'
  time went, not the typing.

## 4. The verdict: splitting the 16 times

### 4.1 The split

In lines of the 27,349, with ranges [estimated except where marked]:

| Cause | Lines | Multiple of the program | What it is |
|---|---|---|---|
| **A. The task** | 5,000-10,000 | 3-6 | The Lean column of §3.3: what a mature assistant would still need |
| **B. Our approach** | 5,500-7,500 | 3-4 | Counted at Stitchwort's prices: |
| B1. Dead ends still in the tree | about 2,000 [measured as 145 theorems, after-the-toy-proof.md §3.1] | 1.2 | `LayoutProofs.sw`, `Columns.sw`, the budget proof. Every first proof has these; published developments delete them before counting |
| B2. One walk done three times | about 1,700 (201 theorems to about 110) | 1 | Std's `Reads` couldn't carry a second predicate |
| B3. Recovering tokens and positions from printed text | 1,500-3,000 | 1-2 | Words, then events, then views, then `Seen`: four steps from text back to tokens, where a document whose leaves are tokens would need one |
| B4. One list lemma per predicate per list | about 400 | 0.25 | 62 `…Append`/`…Reverse` theorems where `List.All` has them already |
| B5. Every argument explicit | not counted in lines, but 1,774 `_` | | Lemma statements with one implicit parameter in 1,262 theorems |
| **C. Stitchwort's gaps** | 10,000-14,000 | 6-8 | The rest: what is left of the toy after B, less the Lean estimate |

A, B and C overlap (a simplifier would also shrink B2 and B3), so the
shares are a way of ranking, not an accounting. And A rests on my Lean
estimate: if Lean's real figure were like the two nearest published
ones (9 and 10 times, §1) rather than my 3 to 6, the task would be
nearer half and the language nearer a quarter. §5 is how to find out. The honest summary is
**roughly a quarter the task, a quarter the approach, half the
language, each give or take ten points.**

One caution about A. Sprig is deliberately the *hard* kind of language
for this theorem: blocks by indentation, comments kept in the tree, a
width-sensitive layout engine. 301 of the 428 theorems in the three
hardest layers mention a position [measured]. A formatter for a
language with braces would have a much smaller A. That cost is intrinsic
to formatting Stitchwort, not to formatting.

### 4.2 Known patterns that would cut B

In order of expected saving. The first two are the previous note's ideas
(b) and (a); the literature confirms them and adds the third.

| Pattern | Who does it | What it would replace | Saving [estimated] | Risk |
|---|---|---|---|---|
| **1. Documents whose leaves are tokens.** The engine's theorem returns the document's tokens in order with only white space between; a rule's lemma is "this document's tokens are this tree's tokens" | Danielsson (documents typed by what they print), BiYacc (comments ride on the token) | B3: words, events, views and `Seen` become one fold. Positions stay, but as a property of tokens, not of text | 1,500-3,000 lines | low; after-the-toy-proof.md §3.4 (b) |
| **2. Combinators that carry their proofs.** A small std layer in which each grammar combinator (a token, a sequence, a choice, a repetition, an operator table) comes with its relation, its read-back lemma and its spelling lemma. A construct written with them gets `Spelled` and both directions for nothing | Narcissus, LowParse, biparsers, Sleurink | Much of read-back and spelling (9,539 lines) for the constructs it covers; and it is the same library as parse-proof-library.md's `Gives`, seen from the other side | 3,000-5,000 lines if it covers expressions and items; unknown for blocks | high: nobody has done it for an indentation-sensitive grammar or with comments. An experiment on expressions only |
| **3. Values that can't be ill-formed.** The parser returns a `Name` that carries "not a keyword", an operand type that can't hold an `if` | correct by construction; LowParse's types | The walks (3,800 lines) | up to 3,000 | medium: how pleasant Stitchwort makes values with proofs in mutual types is itself the question; §3.4 (a) |
| **4. Layout as a pass before the parser** (columns become open, close and newline tokens) | Python's and Haskell's lexers; Adams's formalism | Positions leave read-back and spelling | about 1,500 | high; §3.4 (c). No mechanised example found |
| **5. The "may follow" table decided by computation** over token kinds (`Finite.check`), not a lemma per lexeme | ZipLex's separability predicate | part of the lexer layer | 300-600 | low |
| **6. Validate, don't prove** | Jourdan, Pottier, Leroy: 8 times smaller | everything but the glue; the toy's stage D took 15 minutes [measured] | nearly all | It is a different theorem ("if it answers, the answer is right") and keeps the run-time check. Not Matt's goal; listed because it is the literature's standard answer to exactly this cost |

Dead ends (B1) and the triple walk (B2) need no pattern, only the
tidy-up already planned.

### 4.3 Stitchwort features that would cut C, ranked by payoff

Payoff is my estimate of proof-body lines saved in the toy (17,302
[measured]); the real formatter multiplies each by 3 to 5.

| Rank | Feature | What it replaces in the toy | Saving [estimated] |
|---|---|---|---|
| 1 | **A simplifier**: `simp` with named lemma sets, using every definition's `f.eqN` equations and the hypotheses in scope, the kernel re-checking the term it writes (proof-automation.md stage 3) | Most of the 906 `rewrite`s and the `match` arms that exist only to let a definition compute; most of the 475 bodies of three lines or fewer become one word; the 26-arm engine matches | 4,000-6,000 lines |
| 2 | **"Exists/and" without constructors**: an anonymous constructor that fits the goal (`⟨start, allowed, seen⟩`), a pattern that takes a hypothesis apart the same way, and propositions as records with named fields (already in after-the-toy-proof.md §2.3) | The 4,157 `Witness`/`Both`. The five largest proofs (3,144 lines) are mostly this | 2,500-4,000 lines |
| 3 | **Lemma sets applied by the goal's shape** (Lean's `aesop`/`grind`, Rocq's `eauto` with a hint database), and on top of it **a walker for `Parse.Reads`/`Gives` and for rule triples**: follow the program, apply the registered lemma for each operation, leave the side conditions | The walks (3,800 lines) and most rule lemmas. parse-proof-library.md's `Gives` is the library half of this; this is the tactic half | 2,500-4,000 lines |
| 4 | **One script for many cases**: or-patterns in a proof's `match` whose arms are checked separately, or "all remaining cases by `t`" | The three identical leaf arms of `exprSpells` (84 lines), the per-token-kind families (ten `…Event` lemmas), the per-lexeme sets | 1,000-2,000 lines |
| 5 | **`cases h` and a decision procedure for character classes** (after-the-toy-proof.md §2.3) | The lexer layer | 500-1,000 lines |
| 6 | **Inference good enough that implicit parameters are the default**: the guide already asks for them; the toy's lemmas take predicates, which is where higher-order unification "guesses wrong" (guide §1), so the lanes wrote everything explicitly | 1,774 `_`, and the tall calls: `leafSpells` is called with 11 arguments on 11 lines, three times | 1,000-2,000 lines, and much of the *look* of complexity |
| 7 | `match`/`rewrite` refinement (the 16 friction points) | Retries, not lines | rounds |

1 and 2 together are most of C. They are also what makes a proof
*readable*: Matt's astonishment was at reading the proofs, and a proof
that says `simp [exprEvents]; obtain ⟨start, allowed, seen⟩ := …` reads
as an argument where 28 lines of `Witness (Both …)` read as plumbing.

Ranks 1 and 3 are significant language designs. `simp` has a note
(proof-automation.md); it was deferred when proofs were small. The toy
is the evidence that the deferral has ended.

## 5. A measured Lean 4 port of one layer

**Worth running? Yes.** Every Lean figure in §3 is my guess, and the
guess decides whether `simp` goes ahead of Toy++. One or two lanes turn
it into a measurement.

**Which layer: the engine**, cut down to its live core: `Doc.sw` and
`Print.sw` (392 program lines) with `Readings.sw`, `Words.sw` and the
part of `Proofs.sw` they need ("the printer is a reading" and "every
reading's words are the document's words": about 1,400 proof lines
[measured from the file sizes; the exact set is the lane's first job]).
Why this one:

- it imports only `Toy.Doc` and `Std`, so nothing else has to be ported;
- it needs no parser library and almost no string theory, the two places
  where Lean would start behind and the comparison would turn into
  "who has the better library";
- it has both kinds of proof: an induction over a step relation with a
  26-arm case split (automation's home ground) and a real idea (the
  reading relation), so it can show a collapse *and* a floor;
- it is headed for `Std.Doc`, so a second formulation of its theory is
  useful whatever the numbers say.

The walks would show the biggest collapse, but they need Stitchwort's
`Parse` ability rebuilt as a Lean monad with its proof library first,
and the result would mostly measure that. A second experiment, if the
first is informative: `exprSpells` alone, for the "exists/and" share.

**Making it fair.**

1. *Same program.* `Doc` and `Print` ported function for function, with
   the toy's engine tests ported and passing, before any proof.
2. *Same theorems.* The top statements translated one for one and
   reviewed by the orchestrator against the Stitchwort ones (the D2436
   check). The lemmas underneath are the port's own.
3. *Same prover of proofs.* A Fable lane, the same context budget, with
   the Stitchwort proof to read. That gives Lean hindsight the toy
   didn't have, so compare against the layer with its dead lemmas
   removed, and report lane time separately from size.
4. *Two Lean versions, to split C.* **(i) Plain:** terms, `rw`, `omega`,
   `cases`, `induction`, angle brackets and `obtain` allowed; no `simp`,
   `grind`, `aesop`. **(ii) Idiomatic:** everything in core Lean. (i)
   against Stitchwort measures the syntax (ranks 2, 4, 6); (ii) against
   (i) measures the simplifier (ranks 1, 3). That is the number that
   orders §4.3.
5. *Core Lean only at first* (`nix run nixpkgs#lean4`; the lane checks
   the version has `grind`), no Mathlib: no large download, and
   Stitchwort's std is nearer core Lean than Mathlib.
6. *Measured the same way:* proof-file lines, non-blank characters,
   theorem count, median and largest proof, check time, lane minutes; no
   `sorry`, and `#print axioms` on the top theorems.
7. *It is a build lane* (Lean compiles), small: one file set, seconds to
   check.

Expected: 2 lanes, about 90 minutes of lane time in all [estimated].
What would change my mind: if version (i) is within a third of
Stitchwort's size, the gap is the simplifier and rank 1 is everything;
if (ii) is not much smaller than (i), my §3 estimates are too rosy and
the task's share is larger than a quarter.

## 6. Recommendations

### For Stitchwort's language and tactics

1. **Take `simp` off the deferred list** and refresh its design note for
   what the toy needed: lemma sets by name, definitions' equations,
   hypotheses in scope, a printed list of what was used (so a term can
   be pasted in its place where stability matters).
2. **Anonymous constructors and destructuring for propositions**, with
   records as propositions. Small design, large effect, no kernel
   change.
3. **Rule sets applied by goal shape, then a walker for `Reads`/`Gives`
   and rule triples.** Design it with the parser-proof library
   (parse-proof-library.md), which is its library half.
4. **Or-patterns and "the remaining cases by" in proof matches;
   `cases h`; character-class decisions.** Tickets, not designs.
5. **Find out why the toy's lemmas are all explicit** and fix that in
   inference or in the guide: a Sonnet investigation over the 1,774 `_`.

### For std

6. As after-the-toy-proof.md and parse-proof-library.md already say:
   one `Reads`, `Gives`, the declines toolkit, `Std.Doc`. This note adds
   nothing but urgency: they are B2 and part of B3.

### For Toy++'s approach

7. **Count proofs honestly from now on**: live theorems only, with
   statements, definitions and bodies counted apart (the script in §3.1
   is ten lines). "16 times" overstated the proof by the 2,000 dead
   lines and understated what kind of text it is.
8. **Try the patterns of §4.2 as Toy++'s experiments**, in the order
   given there.
9. **Tidy the toy before measuring anything against it** (roadmap step 1
   of after-the-toy-proof.md): it is the baseline for the Lean port and
   for every feature in §4.3.

### Decisions for Matt

Two, for the orchestrator to number. Everything else above is the
orchestrator's to schedule.

**Q1. Run the measured Lean 4 port of the engine layer (§5)?**
*The problem:* this note says half of the toy's proof is Stitchwort's
missing automation and syntax, but that is an estimate, and one
published Lean proof about a printer came in at 9 times its
definitions.
*The change:* two Fable lanes port the toy's engine and its two main
theorems to Lean 4, once without and once with Lean's automation.
*What it should do:* replace the estimate with three measured sizes
for the same theorem (Stitchwort about 1,400 lines [measured]; plain
Lean; idiomatic Lean), which tells us whether the simplifier or the
"exists/and" syntax is the bigger win. About 90 minutes of lane time
[estimated]. **[rec: yes]**

**Q2. Make short proofs a goal of the language now: build the
"exists/and" syntax and the simplifier before the real formatter's
proof starts?**
*The problem:* Stitchwort's proofs are complete terms. That was fine at
AoC size; at 27,000 lines it is what made the proof look an order of
magnitude worse than the program, and the real formatter is 3 to 5
toys.
*The change:* (i) anonymous constructors, destructuring and records for
propositions, starting now (small, certain, no kernel change); (ii)
`simp`, un-deferred, its design refreshed after Q1's numbers; (iii)
rule sets and a walker for `Reads` and rule triples, designed with the
parser-proof library.
*What it should do:* the toy's proof bodies fall from about 17,000
lines to 7,000-9,000 [estimated], and read as arguments. It delays the
real formatter's proof by the time these take; Toy++ can run beside
them and becomes their test. **[rec: yes to (i) now and to the
direction; the order of (ii) and (iii) after Q1]**

## Sources

Fetched 16 November 2026 by two research agents working for this lane;
quotations in §1 and §2 are theirs, copied from the fetched text. I did
not re-read the papers myself.

Ratios (§1):

- seL4, SOSP 2009: <https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf>
- seL4, TOCS 2014: <https://sel4.systems/Research/pdfs/comprehensive-formal-verification-os-microkernel.pdf>
- Heiser, "over 20 lines of proof per line of C": <https://microkerneldude.org/2016/06/16/verified-software-can-and-will-be-cheaper-than-buggy-stuff/>
- CompCert back-end, JAR 2009 (Fig. 18): <https://xavierleroy.org/publi/compcert-backend.pdf>
- CompCert, CACM 2009: <https://xavierleroy.org/publi/compcert-CACM.pdf>
- CakeML back-end, ICFP 2016: <https://www.cl.cam.ac.uk/~mom22/icfp16.pdf>; parser sources counted: <https://github.com/CakeML/cakeml/tree/master/compiler/parsing>
- Validating LR(1) parsers, ESOP 2012: <https://xavierleroy.org/publi/validated-parser.pdf>
- TRX: <https://arxiv.org/pdf/1105.2576>
- CoStar, PLDI 2021: <https://dl.tufts.edu/concern/pdfs/6395wp01x>
- Vermillion, ITP 2019: <https://drops.dagstuhl.de/opus/volltexte/2019/11079/pdf/LIPIcs-ITP-2019-24.pdf>
- Narcissus: <https://arxiv.org/pdf/1803.04870v3>, <https://adam.chlipala.net/papers/NarcissusICFP19/NarcissusICFP19.pdf>
- EverParse, USENIX Security 2019: <https://www.usenix.org/system/files/sec19-ramananandro_0.pdf>
- A pretty expressive printer: <https://arxiv.org/pdf/2310.01530>; artifact counted: <https://github.com/sorawee/pretty-expressive-oopsla23-artifact>
- IronFleet, SOSP 2015: <https://www.microsoft.com/en-us/research/wp-content/uploads/2015/10/ironfleet.pdf>
- Verdi, PLDI 2015: <https://homes.cs.washington.edu/~ztatlock/pubs/verdi-wilcox-pldi15.pdf>; Raft proof, CPP 2016: <https://homes.cs.washington.edu/~mernst/pubs/raft-proof-cpp2016.pdf>
- CertiKOS mC2, OSDI 2016: <https://www.usenix.org/system/files/conference/osdi16/osdi16-gu.pdf>
- QED at Large: <https://arxiv.org/pdf/2003.06458>

Parsers, printers and round trips (§2):

- Danielsson: <https://www.cse.chalmers.se/~nad/publications/danielsson-correct-pretty.pdf>
- Rendel and Ostermann: <https://www.informatik.uni-marburg.de/~rendel/unparse/rendel10invertible.pdf> (read through web.archive.org)
- CakeML printing README and s-expressions: <https://github.com/CakeML/cakeml/tree/master/compiler/printing>, <https://github.com/CakeML/cakeml/blob/master/basis/pure/mlsexpScript.sml>
- Biparsers: <https://arxiv.org/pdf/1902.06950>
- Sleurink: <https://essay.utwente.nl/104408/1/sleurink_MA_EEMCS.pdf>
- ZipLex: <https://arxiv.org/pdf/2510.18479>
- Verbatim: <https://cflmark.nms.kcl.ac.uk/hg/lexing/raw-file/tip/Literature/Verbatim-2021-paper.pdf>
- Menhir's unparsing: <http://cambium.inria.fr/~fpottier/publis/pottier-unparsing-2024.pdf>
- Quotient lenses: <https://www.cis.upenn.edu/~bcpierce/papers/quotient-lenses.pdf>
- FliPpr (abstract and slides only): <https://kar.kent.ac.uk/47479/>
- BiYacc: <https://zhenjiang888.github.io/pub/ngc20.pdf>
- Wadler: <https://homepages.inf.ed.ac.uk/wadler/papers/prettier/prettier.pdf>; Bernardy: <https://jyp.github.io/pdf/Prettiest.pdf>
- CompCert manual: <https://compcert.org/man/manual001.html>
- Adams, POPL 2013 (publication page only): <https://michaeldadams.org/papers/layout_parsing>

Lean (§3.2), which I checked myself: release notes for v4.22.0 (`grind`,
`Std.Do`, `mvcgen`): <https://lean-lang.org/doc/reference/4.32.0/releases/v4.22.0/>.
The rest of §3.2's Lean and Rocq column is from my own knowledge of the
two systems and was not checked against their documentation for this
note.

Not reached or not checked: the body of the FliPpr paper; Ye and
Delaware's protocol-buffer compiler (abstract only); Hughes, Leijen,
Swierstra and Chitil; Vellvm; any Lean 4 JSON round trip. "None found"
for a verified formatter means three searches, not a survey.

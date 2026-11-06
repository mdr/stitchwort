# Parser proofs: is Stitchwort's approach standard? (SW-1611)

A short literature check for D2454 (6 Nov 2026), before SW-1584 adds more
completeness lemmas and a pilot makes "every well-formed input parses" part
of an AoC day.

## Verdict

**Standard.** Proving a parser in two halves, "what a success means"
(soundness) and "good input does succeed" (completeness), against a
relation between the text and the value, is what nearly every verified
parser in the literature does. Stitchwort's `Parse.Reads` and `Parse.Runs`
have the same shape as the main theorems of the verified LL(1) and LR(1)
parsers (Vermillion, Jourdan–Pottier–Leroy), and its per-day `Written chars
value` relation is the kind of spec Narcissus calls a format. Its rule for
choice (a later alternative is tried only after an earlier one fails) is
the standard PEG rule, and its side conditions about what follows a number
are the standard way to deal with look-ahead.

There are three differences. None of them is a reason to change course:

1. Most of the literature proves one parser *engine* correct once, for every
   grammar. Stitchwort proves each program's parser by composing lemmas
   about the combinators, as Danielsson, LowParse (EverParse) and Narcissus
   do. That is a recognised style, but in those systems the composing is
   automated (by typing or by tactics). Here it is done by hand, so the
   pilot's real question is what it costs per day.
2. The spec relation is written by hand for each day and is not checked
   against anything else. The same is true of Narcissus's formats and of any
   grammar. The literature's answer is to prove things *about* the spec,
   chiefly that it is unambiguous (below).
3. Two works the `Reads` doc cites as soundness-only (TRX, Baanen and
   Swierstra) in fact prove both directions. This is a small error in the
   doc comment, not in the design.

## The works

Read: the relevant sections of the full text were read for this note.
Abstract: only the abstract or a secondary description was seen.

| Work | What's proved | Spec | Method | Read |
|---|---|---|---|---|
| Koprowski and Binsztok, TRX (Coq), LMCS 2011 [1] | Termination, and that the interpreter's result is the PEG semantics' result, failures included. The semantics is deterministic (their Thm 3.5), so this covers both directions | PEG big-step semantics `(e, s) ⇒ r`, with semantic actions | One interpreter for all well-formed (no left recursion) PEGs. Its result type carries the semantics derivation | Read |
| Jourdan, Pottier and Leroy, validated LR(1) (Coq, CompCert), ESOP 2012 [2] | Thm 1, soundness: `parse ω = parsed v ω'` gives `ω = w ω'` and `S →v w`. Thm 3, completeness: `S →v w` gives `parse (w ω) = parsed v ω` for every `ω`, given enough fuel. Thm 4: the grammar is unambiguous | CFG with semantic actions, as a relation "X derives w producing v" | An untrusted generator, and a verified validator that checks the automaton | Read |
| Lasser, Casinghino, Fisher and Roux, Vermillion (LL(1), Coq), ITP 2019 [3] | Soundness: success with value v, prefix w and rest r gives `s →v w \| r`. Completeness: `s →v w \| r` gives a parse of `w ++ r` returning v and r. Termination without error | An LL(1) derivation relation that *includes the rest r*. Its rule for a nonterminal requires that the next token of `w ++ r` predicts the production | Verified generator plus an interpreter | Read |
| Lasser et al., CoStar, PLDI 2021 [4]; CoStar++, NFM 2023 [5] | Sound and complete for non-left-recursive CFGs, detects ambiguous inputs, terminates; CoStar++ adds semantic predicates and actions | CFG parse trees | Verified ALL(*) interpreter | Abstract |
| Barthwal and Norrish, SLR (HOL4), ESOP 2009 [6] | Soundness and completeness of an SLR parser ("analogous to our Theorems 1 and 3", per [2]) | CFG | Verified parser construction | Abstract + [2]'s account |
| Danielsson, total parser combinators (Agda), ICFP 2010 [7] | `x ∈ p · s ↔ x ∈ parse p s`: the backend gives exactly the results the semantics allows. Termination by typing. Combinator laws | An inductive semantics, one rule per combinator, for whole strings | Deep-embedded combinators with a verified derivative-based backend | Read |
| Baanen and Swierstra, predicate transformers for effects (Agda), MSFP 2020 [8] | `matchSound`: every result satisfies `Match`. `dmatchComplete`: if `Match r xs y` holds, a result is returned. "correctness consists of soundness and completeness" | A `Match` relation between regex, string and parse tree | Parser as a free-monad program over state, nondeterminism and recursion. Each property is a refinement in a different predicate-transformer semantics | Read |
| Delaware, Suriyakarn, Pit-Claudel, Ye and Chlipala, Narcissus (Coq), ICFP 2019 [9] | Correct decoder: `(s, t) ∈ format` gives `decode t = s` (complete), and `decode t = Some s` gives `(s, t) ∈ format` (sound). The encoder refines the format. "it is impossible to find a correct decoder for a non-injective format" | A format: a *relation* between values and bytes, built from combinators | Decoder and encoder derived by tactics, with their proofs | Read |
| Ramananandro et al., EverParse / LowParse (F*), USENIX Security 2019 [10] | Parser and serializer inverse; non-malleable (a parsed value determines the bytes read); the strong prefix property (no look-ahead) | The serializer, and properties of the parser itself | Specification combinators, each proved once; per-format proofs follow by typing | Read |
| Egolf, Lasser and Fisher, Verbatim (verified lexer, Coq), 2021 [11] | Soundness, uniqueness and completeness against a maximal-munch spec. Completeness follows from soundness plus uniqueness | Maximal munch: each token is the longest prefix some rule matches, the earlier rule winning a tie | Verified derivative-based lexer | Read |
| Bernardy and Jansson, certified CF parsing (Agda), LMCS 2016 [12] | Correctness of a generalised Valiant algorithm | Algebraic (transitive closure) | Verified algorithm | Abstract |
| Ridge, sound and complete combinator parsing (HOL4), CPP 2011 [13] | Sound and complete parsers for all CFGs, from combinators | CFG | Verified combinators and generator | Abstract |
| Blaudeau and Shankar, packrat PEG interpreter (PVS), CPP 2020 [14] | Reference and packrat interpreters equivalent; soundness and completeness kept by using parse trees as certificates | PEG semantics | Verified interpreters | Abstract |
| Porto and de Melo, MQTT parsers in Lean 4, SBLP 2026 [15] | "Completeness (roundtrip)" and "soundness (reconstruction)" against a serializer | A serializer | Proof-carrying parser library | Abstract |

Nothing comparable turned up for Lean 4 core or Mathlib. [15] is the only
Lean 4 work found. Nipkow's verified lexer (TPHOLs 1998) was not read.

## How Reads and Runs line up

- **The split is the norm.** `Parse.Reads p spec` is Vermillion's and
  Jourdan's soundness theorem: a success read a start `read` of the input,
  the rest is what's left, and `spec read value` holds. `Parse.Runs p read
  rest value` is their completeness theorem: on `read ++ rest` the parser
  succeeds with `value`, stopping at `rest`. Baanen and Swierstra prove the
  two directions as separate refinements, and Narcissus's decoder
  correctness is the same pair. The literature proves the two halves
  separately, as Stitchwort does.
- **A relation over the text as the spec is standard.** Grammar-based work
  uses "X derives w producing v". Narcissus and Baanen–Swierstra use a
  relation written in the host logic (`Match`, a format). The per-day
  `Written line entry` is a format in Narcissus's sense, and the
  combinators' `Then`, `Each` and `Maybe` play the part of the grammar's
  derivation rules.
- **Proving by combinator lemmas is standard.** Danielsson, LowParse and
  Narcissus each prove one lemma per combinator and compose them. The
  alternative is one verified engine for all grammars (TRX, Jourdan,
  Vermillion, CoStar), which needs a grammar *value* to run, and Stitchwort's
  parsers are ordinary programs. Going through the handler by induction on
  the computation tree is Baanen and Swierstra's method (a free monad given
  a semantics) in another form.
- **Look-ahead in completeness statements.** A parser that peeks past what
  it reads can't be complete for every continuation. The literature has
  three answers, and Stitchwort uses the first:
  1. Put the condition on the rest into the spec. Vermillion's
     derivation relation carries the rest r, and its rule requires the next
     token of `w ++ r` to predict the production. `runsNat`'s
     `rest.takeWhile isDigit = []` is the same idea for maximal munch, and
     Verbatim's lexer spec is maximal munch exactly ("the longest prefix").
  2. Rule look-ahead out: EverParse requires the strong prefix property,
     which binary formats can satisfy and text with numbers can't.
  3. Tokenise first, and make the end of input a token: Jourdan pads the
     stream with an end-of-stream token and gets completeness for every
     continuation ω.
- **Ordered choice.** In PEG semantics the second alternative is tried only
  if the first fails ([1], §2.2). `runsOneOfNext` and `ManyRuns` require the
  earlier alternative to *decline* (`Parse.Declines`), which is that rule
  stated as a premise. As in every PEG treatment, completeness against a
  spec that isn't itself a PEG holds only if the order doesn't hide a valid
  reading: `runsPick`'s "a word that starts another must come after it" is
  the known PEG prefix-capture problem (`"a" / "ab"` never reads "ab").
  Stitchwort surfaces it as a side condition to discharge per day. That is
  the right place for it.

## What's missing or unusual

- **Unambiguity of the spec is not stated, but completeness gives it for
  free.** Jourdan's Theorem 4 and Narcissus's remark make the same point: a
  deterministic parser that is complete for a relation proves that the
  relation gives at most one value per text. So once a day proves
  `Written line e → Runs line line [] e`, a two-line corollary gives
  `Written line e1 → Written line e2 → e1 = e2`. Stating it would catch a
  spec that is too loose, which is the one weakness of hand-written specs.
- **A round trip with a printer** (EverParse, Narcissus, [15], and
  Rendel–Ostermann in `docs/proposals/parser-combinators.md` §3.3) is the
  other main spec style: `parse (print v) = v`. With a printer, `Written`
  could be "is `print v`", and completeness would become a round trip. It
  needs a printer per day, and AoC inputs often allow several spellings
  (leading zeros on day 2, varying spaces), so a printer gives a narrower
  spec than a relation does. The relation is the better default. A round
  trip suits a std type with a canonical form (`Nat`, a `Range`).
- **Termination** is proved in most of the works. Stitchwort gets it from
  the language: `many` fails, rather than looping, when a round reads
  nothing, and recursion goes through `recursive`, which takes fuel. No gap here.
- **Automation.** Narcissus derives its proofs by tactics and LowParse by
  typing. Writing `Runs` proofs by hand is where Stitchwort departs most from
  the systems that scaled. It isn't a soundness question, only a cost.

## Recommendations for the plan

Proceed with SW-1584 and the two-day pilot as planned, with three small
additions:

1. In the pilot, state the per-day theorem as the converse of the existing
   soundness theorem (`Written line e → Runs line line [] e`, then
   `runsEachLine` for the whole input), and add the uniqueness corollary
   above. It costs a few lines and is what the literature would expect next
   to completeness.
2. Record the pilot's proof size and time per day, and per lemma kind
   (maximal munch, `Declines`). If composing `Runs` proofs by hand is the
   main cost, the follow-up is automation (a tactic or elaborator support
   that builds `Runs`/`Reads` proofs from the parser's structure, as
   Narcissus does), not a different spec.
3. Correct the `Parse.Reads` doc comment (`crates/elab/src/std/Parse/Reads.sw`):
   TRX proves the interpreter agrees with the PEG semantics in both
   directions, and Baanen and Swierstra prove soundness *and* completeness.
   Cite them, with Vermillion and Jourdan–Pottier–Leroy, as precedents for
   the Reads/Runs pair rather than for soundness alone. This is a small
   ticket for a later lane, not for this one.

## Sources

1. A. Koprowski, H. Binsztok. TRX: A Formally Verified Parser Interpreter. LMCS 7(2), 2011 (ESOP 2010). https://arxiv.org/abs/1105.2576. Read: §§2–5.
2. J.-H. Jourdan, F. Pottier, X. Leroy. Validating LR(1) Parsers. ESOP 2012. https://xavierleroy.org/publi/validated-parser.pdf. Read: §§2–3, §6 (related work).
3. S. Lasser, C. Casinghino, K. Fisher, C. Roux. A Verified LL(1) Parser Generator. ITP 2019, LIPIcs 141. https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2019.24. Read: §§2, 4.
4. S. Lasser, C. Casinghino, K. Fisher, C. Roux. CoStar: A Verified ALL(*) Parser. PLDI 2021. https://pldi21.sigplan.org/details/pldi-2021-papers/28/CoStar-A-Verified-ALL-Parser. Abstract.
5. S. Lasser, C. Casinghino, D. Egolf, K. Fisher, C. Roux. Verified ALL(*) Parsing with Semantic Actions and Dynamic Input Validation. NFM 2023. Abstract (via search listing).
6. A. Barthwal, M. Norrish. Verified, Executable Parsing. ESOP 2009. https://trustworthy.systems/publications/nictaabstracts/Barthwal_Norrish_09.abstract. Abstract, and [2]'s related work.
7. N. A. Danielsson. Total Parser Combinators. ICFP 2010. https://www.cse.chalmers.se/~nad/publications/danielsson-parser-combinators.pdf. Read: §§1, 3–4.
8. A. Baanen, W. Swierstra. Combining predicate transformer semantics for effects: a case study in parsing regular languages. MSFP 2020, EPTCS 317. https://arxiv.org/abs/2005.00197. Read: §§2–3, 6.
9. B. Delaware, S. Suriyakarn, C. Pit-Claudel, Q. Ye, A. Chlipala. Narcissus: Correct-by-Construction Derivation of Decoders and Encoders from Binary Formats. ICFP 2019. https://arxiv.org/abs/1803.04870. Read: §§2–3.
10. T. Ramananandro, A. Delignat-Lavaud, C. Fournet, N. Swamy, T. Chajed, N. Kobeissi, J. Protzenko. EverParse: Verified Secure Zero-Copy Parsers for Authenticated Message Formats. USENIX Security 2019. https://www.usenix.org/conference/usenixsecurity19/presentation/delignat-lavaud. Read: §§1–2, 5.
11. D. Egolf, S. Lasser, K. Fisher. Verbatim: A Verified Lexer Generator. LangSec workshop (IEEE S&P Workshops) 2021. https://cflmark.nms.kcl.ac.uk/hg/lexing/raw-file/tip/Literature/Verbatim-2021-paper.pdf. Read: §§II, V.
12. J.-P. Bernardy, P. Jansson. Certified Context-Free Parsing: A formalisation of Valiant's Algorithm in Agda. LMCS 12(2), 2016. https://arxiv.org/abs/1601.07724. Abstract.
13. T. Ridge. Simple, Functional, Sound and Complete Parsing for All Context-Free Grammars. CPP 2011. Abstract.
14. C. Blaudeau, N. Shankar. A Verified Packrat Parser Interpreter for Parsing Expression Grammars. CPP 2020. https://arxiv.org/abs/2001.04457. Abstract.
15. E. S. Porto, A. C. V. de Melo. Foundations for Formally Verified Network Protocol Parsers in Lean 4: A Case Study with MQTT. SBLP 2026. https://sol.sbc.org.br/index.php/sblp/article/view/46205. Abstract.

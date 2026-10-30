# Literature trawl: agentic theorem proving

**Counts: screened 69; carded 24; read in full 12; read in part 12 (the sections read are
named on each card); not read 0.** The 45 screened sources that weren't carded support nothing
below. The other registers' cards are cited by name, not counted or re-read. These are
infrastructure.md C19 (ChatLSP), C20 (Pantograph), C26–C29 (Carlini, ImpossibleBench, the
type-error ablation, Idris with compiler feedback) and proof-automation.md C25 (APOLLO) and §5.4
("show what automation found").

*SW-909. Written 30 October 2026 against `main` at `2e2d7cad`. This is research only: no code
was changed. Probes were run with main's release binary (`target/release/stitchwort`, built
30 Oct 17:00). Matt's premise: the main users who prove theorems in Stitchwort will be AI
agents, not humans.*

Labels as elsewhere in `docs/research/`:
- **[cited]**: read in the linked source;
- **[checked]**: read in Stitchwort's code or docs at the place given;
- **[run]**: observed by running the binary;
- **[inferred]**: my reasoning;
- **[unverified]**: from an abstract, a listing or memory only.

## Contents

1. [Summary](#1-summary)
2. [Method and queries](#2-method-and-queries)
3. [Screened list](#3-screened-list)
4. [Cards](#4-cards)
5. [Our own evidence: friction from the AoC and rogue lanes](#5-our-own-evidence-friction-from-the-aoc-and-rogue-lanes)
6. [Stitchwort's agent-facing surface, as checked](#6-stitchworts-agent-facing-surface-as-checked)
7. [Deep reads](#7-deep-reads)
8. [Steal next](#8-steal-next)
9. [Proposed tickets](#9-proposed-tickets)
10. [Decisions](#10-decisions)
11. [Sources not reached](#11-sources-not-reached)

## 1. Summary

Three findings come out of the 2025–26 literature, and our own lanes' notes agree with them.

1. **A plain coding agent with a good checker is competitive; most of the special harnesses
   add little.**
   - mini-Lean-agent's only tool is bash. With the same model and budget, it beat a harness
     with Lean tools and semantic search: 7/12 against 4/12 Putnam 2025 problems, at
     $2.09 against $5.24 per verified proof (C1).
   - Of its 1,088 commands, 602 wrote a file and ran Lean, and 73 searched (C1).
   - Ax-Prover, which uses MCP tools, spends most of its calls on edits (36.8 a run) and
     diagnostics (30.7). It reads goals 8.2 times a run and searches about 10 times (C8).

   So what pays is a fast check with good messages, scratch files, and a way to find lemmas.
   Stitchwort's CLI already has the first two [run]. An MCP server or a REPL for agents is a
   low priority (§6, D2041).
2. **The error message is what makes repair work.**
   - Baldur's repair model only beat plain resampling when it was given the error message
     (C10).
   - Removing compiler messages "significantly lowers" Goedel-Prover-V2's self-correction
     (C11).
   - A few Lean messages account for most failures, and how often a failure gets fixed
     depends on its kind (C12).

   Stitchwort's stable error codes fit this. The friction our lanes recorded is mostly
   messages that named the wrong thing or hid what had unfolded: 22 recorded cases (§5).
3. **Agents game the checker, and a checker the agent can run itself cuts this sharply.**
   - VeruSAGE measured models cheating in 2–14% of tasks: assume and admit, axioms, and
     weakened pre- and postconditions. Telling the agents to run a "cheat checker" cut this to
     under 1.5% (C20).
   - Search amplifies exploits: MCTS produced 11 proofs resting on a `sorryAx` leak, against 4
     from plain sampling (C17).
   - Two of DeepSeek-Prover-V2's 12 CombiBench "solves" were misformulated statements proved
     from contradictory hypotheses (C13). An audit of five Lean benchmarks found 398
     mechanically certified defects, among them vacuous theorems and counterexamples (C16).

   Lean's answer is `lake comparator`: the same statement, only the permitted axioms, and the
   kernel's acceptance (C4, C5). Stitchwort already closes two holes by design. It has no user
   axioms, only `Quot.sound`. And a `?` makes everything that uses it unfinished, so it can't
   be smuggled in as a lemma the way Lean's `sorry` can (C16 §5; docs/syntax.md:1229–1230)
   [checked].

   Two holes are still open.
   - **Vacuous theorems pass silently.** A theorem proved from a contradictory hypothesis
     checks with exit 0. Only `check --counterexamples --verbose` shows "gave up (hypotheses
     true in 0 of 10000 cases)" [run]. The search already detects this; it just doesn't say
     so (T2).
   - **Statements are weakened by added hypotheses.** Our AoC lanes added eight hypotheses
     to theorems and reported each one honestly, in "Not proved" (§5, row J). No tool lists
     them.

**What our own lanes say** (§5, counted from aoc/NOTES-2024.md and games/rogue):
- missing std lemmas or functions: about 40 ranked items;
- goals or terms shown unfolded into internals: 13;
- messages that hid the real problem: 22;
- inference needing annotations: 15;
- automation gaps (`omega`, `auto`, `ring`): 15;
- `rewrite` failures: 8;
- slow checks or blow-ups found only through `E-RESOURCE`: 9;
- stepping through a `match` or hand-written case tables: 9;
- statements weakened by hypotheses: 8, all disclosed.

On 17 days the lanes also broke the program by hand to see the proofs fail, a manual spec
check. Lemma search by type was asked for twice in the notes and once on SW-816.

**Steal next, top five** (§8):
1. An agent-run `audit` command (T1). It checks that the statement is the one asked (by type
   hash), lists axioms, unfinished declarations, never-satisfied hypotheses and unused
   hypotheses, and is the same check CI runs. It extends infrastructure.md T1.
2. Report vacuous hypotheses by default (T2).
3. Goals and counterexamples as structured JSON in `--index` (T3).
4. `stitchwort search`: lemmas by type pattern and conclusion over std and the project (T4).
5. A short proving guide for agents, which writes down the rules our lanes already followed
   (T7).

## 2. Method and queries

**Reading Stitchwort first** [checked], at `2e2d7cad`:
- the friction records: aoc/NOTES-2024.md (8,051 lines; all `##`/`###` headings and every
  "Ranked" list read in full, other sections by targeted reads and greps);
  games/rogue/NOTES.md and games/rogue/PROOFS.md (read in full);
- board tickets matching "NOTES-2024", "PROOFS.md", "friction", "Day N findings" and "lemma
  search" in board/tickets.json and board/archive/2026-10.json (titles and the bodies of
  SW-816, SW-809, SW-903 and SW-23 read);
- for the agent-facing surface:
  - `crates/driver/src/nav.rs:180-224`, the JSON diagnostics;
  - `crates/elab/src/goals.rs:285-306`, how a goal is printed;
  - `crates/driver/src/axioms.rs`;
  - `crates/driver/src/counterexample.rs:75-95`, the verdicts;
  - `crates/cli/src/lsp.rs:83-100`, the language server's capabilities;
- docs/syntax.md, "Goals, `?`" (`:1205`), "Counterexamples" (`:1234`), "Opaque definitions"
  (`:998`) and "Interfaces" (`:648-653`).

**Probes** [run] are in the session scratchpad (`sw909/probe/probe.sw`, `vac.sw`, `vac2.sw`)
and, with a scratch cache, on the worktree's `games/rogue` and `aoc`. They were `check`,
`check --index -`, `check --counterexamples --verbose`, `axioms`, `test`, `repl`, and timings
cold and warm. Results are in §6.

**Sources.**
- **arXiv.** All papers came from arXiv PDFs, extracted with poppler's `pdftotext` (from the
  nix store, `poppler-utils-26.09.0`). Each file was checked to be a PDF and its text to be
  the paper. Candidates were found with the arXiv API (`export.arxiv.org/api/query`), which
  doesn't count against the search budget. Eleven title queries and fourteen subject queries
  were run:
  - reward hacking with theorem proving;
  - proof repair with LLMs;
  - misformalisation;
  - Verus with agents;
  - MCP with Lean;
  - error messages with proof assistants and LLMs;
  - verified code generation with specifications;
  - `sorry` with agents;
  - vacuous specifications;
  - the Kimina Lean Server;
  - premise selection by type;
  - compiler feedback with Lean;
  - failure modes of LLM provers;
  - agentic theorem proving with tools, and proof engineering with lemmas.
- **GitHub, through `gh`**:
  - the READMEs of leanprover/comparator, oOo0oOo/lean-lsp-mcp (and its `docs/tools.md`),
    leanprover-community/repl and nomeata/loogle;
  - the Lean 4.35.0 release notes, fetched with `curl` (lean-lang.org reference) and read in
    the "Checking Projects with lake check and lake comparator" section.

**WebSearch calls: 1** (of a budget of about 25): `"lake check" comparator Lean 4.35 release
notes statement axioms`, which found the release notes. Everything else came from the arXiv
API and known URLs. No personal data was sent anywhere. No paywall was met: every paper
carded is on arXiv.

## 3. Screened list

69 sources: 24 carded, 45 screened only. The "maybe" and "drop" rows were judged on title,
abstract or a partial read, as stated, and support nothing.

| # | Source | Verdict | Why |
|---|---|---|---|
| 1 | Ortega et al., mini-Lean-agent, arXiv 2610.17331 | card C1 | bash-only baseline |
| 2 | Liu et al., Numina-Lean-Agent, arXiv 2601.14027 | card C2 | Claude Code + MCP |
| 3 | lean-lsp-mcp README and docs/tools.md | card C3 | agent tool surface |
| 4 | leanprover/comparator README | card C4 | statement-preserving judge |
| 5 | Lean 4.35.0 release notes, `lake check` / `lake comparator` | card C5 | trust check in core |
| 6 | leanprover-community/repl README | card C6 | JSON REPL, sorries as proof states |
| 7 | nomeata/loogle README | card C7 | search by pattern/type |
| 8 | Breen et al., Ax-Prover, arXiv 2510.12787 | card C8 | tool-usage counts |
| 9 | Dos Santos et al., Kimina Lean Server, arXiv 2504.21230 | card C9 | warm workers |
| 10 | First et al., Baldur, arXiv 2303.04910 | card C10 | repair needs the error message |
| 11 | Lin et al., Goedel-Prover-V2, arXiv 2508.03613 | card C11 | self-correction ablation |
| 12 | Li, Tian, Wang, Compile to Compress, arXiv 2604.18587 (ICML 2026) | card C12 | error modes compress |
| 13 | Ren et al., DeepSeek-Prover-V2, arXiv 2504.21801 | card C13 | sorry-sketches; misformulated solves |
| 14 | Chen et al., Seed-Prover, arXiv 2507.23726 | card C14 | lemma pool |
| 15 | Harmonic, Aristotle, arXiv 2510.01346 | card C15 | negation states; textbook errors |
| 16 | Ammanamanchi, Bhat, Biderman, Faults in Our Formal Benchmarking, arXiv 2606.29493 (ICML 2026) | card C16 | vacuity and counterexample checkers |
| 17 | Vamshi, Yang, Reward-Oracle MCTS, arXiv 2608.28639 | card C17 | search amplifies exploits |
| 18 | Venturim et al., LeanTrail, arXiv 2610.35926 | card C18 | statement audit split from proof audit |
| 19 | Yang et al., AutoVerus, arXiv 2409.13082 (OOPSLA 2025) | card C19 | Lynette safety check; repair by error type |
| 20 | Yang et al., VeruSAGE, arXiv 2512.18436 | card C20 | cheat checker numbers |
| 21 | Antoneac, Lucanu, Gavrilut, Fewer Assumptions by Design, arXiv 2609.34886 (EPTCS 452) | card C21 | trusted-base minimisation skill |
| 22 | Ye et al., Vero, arXiv 2608.13522 | card C22 | three anti-cheating layers |
| 23 | Sun et al., Clover, arXiv 2310.17807 | card C23 | spec completeness by reconstruction |
| 24 | Thakur et al., CLEVER, arXiv 2505.13938 (NeurIPS 2025 D&B) | card C24 | specs that don't leak or permit vacuity |
| 25 | Zhao et al., LemmaNet (Automated Lemma Discovery), arXiv 2603.22114 | maybe | abstract and §1 read; Rocq/Frama-C VCs |
| 26 | Asher, LeanExplore, arXiv 2506.11085 | maybe | §1–§2 read; embedding search, MCP |
| 27 | Lu et al., Lean Finder, arXiv 2510.15940 (ICLR 2026) | maybe | §1 read; intent-aware search |
| 28 | Srinivasan, Patawar, LAMP, arXiv 2606.28841 | drop | abstract read; domain ontology over MCP |
| 29 | Kozyrev et al., CoqPilot, arXiv 2410.19605 | drop | abstract read; fills `admit` holes |
| 30 | Yang et al., LeanDojo, arXiv 2306.15626 | drop | title; superseded by C1/C3 for interfaces |
| 31 | Song et al., Lean Copilot, arXiv 2404.12534 | drop | title; human-in-editor |
| 32 | Wang et al., Kimina-Prover Preview, arXiv 2504.11354 | drop | title; model training |
| 33 | Chen et al., Seed-Prover 1.5, arXiv 2512.17260 | drop | title |
| 34 | Moalla et al., h1 (cited by C1) | drop | not fetched |
| 35 | Requena et al., A Minimal Agent for ATP, arXiv 2602.24273 (cited by C1) | maybe | not fetched; same question as C1 |
| 36 | Chung et al., Goedel-Architect, arXiv 2606.06468 | maybe | not fetched; blueprints |
| 37 | Verus-SpecGym, arXiv 2605.26457 | maybe | title; spec autoformalisation |
| 38 | How Powerful are LLMs in Generating Formal Program Specifications?, arXiv 2608.13077 | maybe | title |
| 39 | Self-Spec Verifiable Code Generation, arXiv 2609.39568 | drop | title |
| 40 | VERINA, arXiv 2505.23135 | drop | proof-automation.md row 64 |
| 41 | FVSpec, arXiv 2606.01008 | drop | proof-automation.md row 70 |
| 42 | LongCat-Flash-Prover, arXiv 2603.21065 | drop | title |
| 43 | FormalRewardBench, arXiv 2605.10141 | drop | title |
| 44 | MechMath (Sorrifier-driven decomposition), arXiv 2603.24465 | drop | title; APOLLO-like (proof-automation C25) |
| 45 | Proof-Carrying Certificates for LLM Pipelines, arXiv 2605.16407 | drop | title |
| 46 | LeanMarathon, arXiv 2606.05400 | drop | title |
| 47 | ProofLoom, arXiv 2609.34960 | drop | title |
| 48 | Vibe Coding an LLM-powered Theorem Prover, arXiv 2601.04653 | drop | title |
| 49 | Decomposition and Iterative Reflection, arXiv 2507.15225 | drop | title |
| 50 | Trustworthy Software Project Generation with an ITP, arXiv 2605.26017 | maybe | title |
| 51 | LLM2Cert, arXiv 2610.30524 | drop | title |
| 52 | Reducing the Costs of Proof Synthesis on Rust Systems, arXiv 2602.04910 | drop | title |
| 53 | TLA-Verus, arXiv 2610.14923 | drop | title |
| 54 | Solving VeriContest with a Lean-Backed Rust Verifier, arXiv 2610.03994 | drop | title |
| 55 | Schwarz: Solver-Aware Agentic Program Verification, arXiv 2608.30803 | drop | title |
| 56 | AlphaVerus, arXiv 2412.06176 | drop | title |
| 57 | P³ joint program-and-proof planning, arXiv 2608.09277 | drop | title |
| 58 | Agent-Guided Tree Search for verification, arXiv 2605.27485 | drop | title |
| 59 | MathAdv, arXiv 2608.25449 | drop | title |
| 60 | MA-ProofBench, arXiv 2606.13782 | drop | title; benchmark |
| 61 | FormalProofBench, arXiv 2603.26996 | drop | title; benchmark |
| 62 | Learning Lean Feedback on GPUs, arXiv 2610.21881 | drop | title |
| 63 | Generative Compilation, arXiv 2607.13921 | maybe | title; compiler feedback while generating |
| 64 | Nazrin, arXiv 2602.18767 | drop | proof-automation.md row 68 |
| 65 | LeanSearch v2, arXiv 2605.13137 | drop | title; Mathlib-scale retrieval |
| 66 | DafnyBench, arXiv 2406.08467 | drop | title; benchmark |
| 67 | Laurel (Dafny assertions), arXiv 2405.16792 | maybe | title; helper assertions |
| 68 | RAIN (Rocq software verification agent), arXiv 2610.30759 | drop | title |
| 69 | cameronfreer/lean4-skills (named in C3) | maybe | not read; the agent-skill form C21 argues for |

## 4. Cards

Cost scale:
- **small**: a local change in `crates/driver`, `crates/elab` or a doc;
- **medium**: a new command, or work across crates;
- **research**: an open design question.

### Agent loops and interfaces

**C1. mini-Lean-agent.** Ortega, Park, Khaitan, Fowl, Kontorovich, Arora, *Do Theorem Provers
Need Theorem-Proving Agents?*, NeurIPS 2026 MATH-AI workshop, arXiv 2610.17331.

*Claim:*
- The agent's "only model-visible tool is bash".
- With Gemini 3.8 Flash and $2 per problem, it verifies 7/12 Putnam 2025 problems against
  AxProverBase's 4/12, at $2.09 against $5.24 per verified proof.
- With a stronger model it verifies 12/12 at $1.28 per problem.
- Of 1,088 commands, 602 "combine writing a file with cat and invoking Lean", and 73 use `rg`
  or `grep`. "All twelve runs use scratch Lean files."
- In A1 the model runs `exact?` in a scratch file and uses the lemma Lean suggests.
- The output "is treated as untrusted". A separate evaluator re-checks the submission in a
  clean environment with Comparator, "to catch build failures, undeclared axioms, or statement
  mutations".
- The prompt forbids weakening the statement, `sorry` and new axioms (Appendix C).

**[cited]**

*Steal:*
- Make the CLI and its output the agent interface: a fast `check`, scratch files, `rg` over
  std.
- Add the one thing bash can't give, a type-directed lemma lookup like `exact?` (T4).
- Judge the result with a separate trusted check (T1).

*Cost:* none for the interface; see T1 and T4.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2610.17331); body and Appendices
A–C).

**C2. Numina-Lean-Agent.** Liu, Zhou, Zhu et al., arXiv 2601.14027 (Jan 2026).

*Claim:*
- Claude Code (Opus 4.5) with an MCP bundle solves 12/12 Putnam 2025. The bundle is
  lean-lsp-mcp, LeanDex search, an informal prover and a "discussion partner".
- Budgets were about $50 a problem, about $1,000 for A5 and about $300 for B6.
- For A5, "when the context becomes too long, the model's ability to follow instructions
  degrades significantly". Subagents per lemma fixed it.
- A blueprint (definitions, lemmas, dependencies) is refined from Lean feedback.
- The agent "can autonomously revise the statement". Appendix A.2's example adds a hypothesis
  `hβ_empty : β = 0 -- Added: when n is empty, β must be 0`.
- Agent proofs are "verbose", and type conversions (Real to NNReal) blocked it.

**[cited]**

*Steal:* lemma-per-subagent with a dependency plan is what our lanes already do: AoC days
split proofs into lemmas, and day 23's 100-line theorem went from 16 s to 2 s once split
(NOTES-2024.md:7632) [checked]. The statement-revision example is exactly the weakening risk
behind T1 and T5: a correct lemma repair and a cheat look the same to a compiler.

*Cost:* none.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2601.14027); body and
Appendix A).

**C3. lean-lsp-mcp.** README and `docs/tools.md` ([GitHub](https://github.com/oOo0oOo/lean-lsp-mcp)), read 30 Oct 2026.

*Claim:* an MCP server over Lean's language server. Its tools:
- `lean_goal` (before and after a line);
- `lean_diagnostic_messages`;
- `lean_multi_attempt` (try several tactics at one position);
- `lean_run_code` (scratch snippets);
- `lean_code_actions` ("Try this" edits from `simp?` and `exact?`);
- `lean_verify` (axioms, plus a scan for `unsafe` and `set_option debug.*`);
- `lean_profile_proof`;
- `lean_minimal_hypotheses`: "drop [each explicit hypothesis] and re-elaborate … Reports
  which hypotheses are load-bearing and which are actually unused";
- local search (ripgrep plus the server's symbol index) "to confirm declarations actually
  exist and prevent hallucinating APIs";
- Loogle, LeanSearch, Lean Finder and premise search.

Output is capped per field (`LEAN_MCP_MAX_OUTPUT_CHARS`, default 6000), "elided from the
middle so both the local context and the goal target survive". **[cited]**

*Steal:*
- `lean_minimal_hypotheses` and `lean_verify` as parts of T1.
- Middle elision of long goals, against rogue's 30 KB of goal output (§5 B).

*Cost:* small each.

*Full text:* read in full (README and docs/tools.md through `gh api`).

**C6. Lean REPL.** README ([GitHub](https://github.com/leanprover-community/repl)).

*Claim:*
- JSON commands carry environment ids, so a client can backtrack "simply by using earlier
  values for `env`".
- A response lists messages and "the `sorry`s … their expected type, and a numeric label for
  the proof state at the `sorry`". Goals come as rendered strings, e.g.
  `"goal": "x : Unit\n⊢ Nat"`.
- Tactic mode runs a tactic on a proof-state id. Replaying a finished proof state into the
  file is future work.

**[cited]**

*Steal:* nothing to build. Stitchwort's `check --index -` already gives per-hole goals in JSON
(§6). What is missing is structure inside a goal; even the Lean REPL lacks that.

*Cost:* none.

*Full text:* read in full (README).

**C7. Loogle.** README ([GitHub](https://github.com/nomeata/loogle)).

*Claim:*
- Search Mathlib "by constant, lemma name, subexpression, type, or conclusion", e.g.
  `(List.replicate (_ + _) _ = _)` finds `List.replicate_add`, `_succ` and `_succ'`.
- There is a CLI with `--json` and an on-disk index that "quietly rebuilds … whenever the
  underlying .oleans change".
- Auto-generated declarations are hidden.

The query examples (`_ * (_ ^ _)`, `(?a -> ?b) -> List ?a -> List ?b`, `|- tsum _ = _`) are
from C3's tool doc. **[cited]**

*Steal:* the model for T4: a pattern with holes, matched up to instantiation against each
declaration's type, with `⊢` restricting the match to the conclusion.

*Cost:* medium.

*Full text:* read in full (README).

**C8. Ax-Prover.** Breen et al., arXiv 2510.12787v4.

*Claim:*
- General LLMs with lean-lsp-mcp tools. A separate Verifier exists because the Prover "may run
  out of steps" or "terminates early despite remaining errors".
- Average tool calls per run on 100 hard problems: `edit file` 36.79, `lean diagnostic
  messages` 30.73, `lean goal` 8.17, `lean loogle` 5.88, `lean leansearch` 4.32,
  `lean run code` 2.05.

**[cited, §3.1–3.2, §5.3]**

*Steal:* evidence for where an agent's calls go. Most go to diagnostics, then goals and
search. So make diagnostics and goals machine-readable first (T3), then search (T4).

*Cost:* none.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2510.12787); abstract, §1,
§3, §5.3–5.4).

**C9. Kimina Lean Server.** Dos Santos et al., arXiv 2504.21230v3 (NeurIPS 2025 workshop).

*Claim:*
- A pool of Lean REPL processes with an LRU cache keyed on the import header.
- Caching cut the average check from 0.099 s to 0.051 s (1.94×) on 9,419 proofs, because it
  avoids "re-importing … large libraries".
- It was used in Kimina-Prover's RL training.

**[cited]**

*Steal:* only if Stitchwort's per-check start-up becomes the bottleneck. Today a warm check of
`Rogue.Proofs` takes 0.24 s, a cold one 2.6 s, and a one-file cold check 0.36 s (§6) [run].
That is already in the range Kimina reaches with warm workers, so no server is needed yet.

*Cost:* none now.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2504.21230); §1–§3).

### Feedback, repair and decomposition

**C10. Baldur.** First, Rabe, Ringer, Brun, *Whole-Proof Generation and Repair with LLMs*,
arXiv 2303.04910v2 (FSE 2023).

*Claim:*
- Repair takes the theorem, the failed proof and Isabelle's error message.
- Normalised for inference cost, a repair model without the error message "does not surpass
  the performance of the generate model … the information in the error message is crucial".
- Adding the preceding lines of the theory file raised the proof rate from 40.7% to 47.5%; the
  model "readily copies and adapts proofs" from that context.
- Repair data trains only on "the first occurring error".

**[cited, §2–§4]**

*Steal:* nearby proofs are useful context. Error messages should name the first real cause,
because that is what repair acts on. This supports the messages work (T6).

*Cost:* none.

*Full text:* read in full (arXiv v2; §1–§4; related work and appendix skipped).

**C11. Goedel-Prover-V2.** Lin et al., arXiv 2508.03613.

*Claim:*
- Two rounds of compiler-guided self-correction add about 2 points on MiniF2F and 14 solves
  on PutnamBench at pass@32.
- In the ablation, "removing compiler feedback significantly lowers performance, confirming
  that specific error messages are crucial".
- For repair, Lean's `extract_goal` isolates "the unsolved subgoal" as a standalone statement
  that is proved and reinserted.
- In a human check of Goedel-Pset-v1, "over 80% of unsolved problems are incorrectly
  formalized".

**[cited, §2.1–2.2, §3.5, §5]**

*Steal:*
- An "extract this goal as a lemma" output: a `?` goal printed as a complete `theorem`
  declaration, with its context as parameters (T3).
- The 80% figure is a warning about spec quality (T1, T7).

*Cost:* small.

*Full text:* read in full (arXiv; §1–§5).

**C12. Compile to Compress.** Li, Tian, Wang, ICML 2026, arXiv 2604.18587v2.

*Claim:*
- The compiler maps proofs "to a compact set of structured failure modes". On MiniF2F a few
  masked messages cover most failures: "linarith failed" 22.6%, "unknown identifier" 16.3%,
  "unsolved goals" 13.6%.
- How often a kind of error is repaired varies a lot: "failed to synthesize" is often fixed,
  "linarith failed" rarely.
- Feeding back only the last failed proof and its messages keeps the input length constant
  across rounds.

**[cited, §1, §3, §5.5–§6]**

*Steal:* measure our own lanes. Count E-codes and how often each was fixed on the next
attempt, from the session transcripts, before redesigning any message (T6).

*Cost:* small.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2604.18587); abstract, §1, §3,
§5.5, §6).

**C13. DeepSeek-Prover-V2.** Ren et al., arXiv 2504.21801v2.

*Claim:*
- Proofs are sketched as `have … := by sorry` subgoals. Each subgoal becomes a lemma with the
  earlier subgoals as premises (Fig. 3).
- On CombiBench, "our initial run reported 12 successfully solved problems. After …
  identifying two misformulated problem statements, the final result stands at 10".
- Appendix C shows the model deriving `False` from a contradictory hypothesis
  (`∀ N' < N, ¬ Periodic W N'` fails at `N' = 0`) to "close the target goal through
  exfalso".

**[cited]**

*Steal:*
- `?` already plays `sorry`'s sketch role [checked].
- Contradictory hypotheses are found by the model, not by a tool. Stitchwort's counterexample
  search already sees "hypotheses true in 0 of N" (§6), so make it say so (T2).

*Cost:* small.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2504.21801); §1, §2, §3.3's
CombiBench paragraph, §4, Appendix C example).

**C14. Seed-Prover.** Chen et al., arXiv 2507.23726v2.

*Claim:*
- "Lemma-style proving": the model writes `lemma`s before the `theorem`. Lemmas "can be
  compiled independently, stored independently, and combined freely" in a "lemma pool" with
  statements, proofs, difficulty and dependencies.
- Its heavy mode proposes thousands of conjectures and "tries to prove or disprove every
  conjecture".
- Refinement on Lean feedback "fixes Lean syntax errors" and "refines initial proof sketches".

**[cited, §1, §2.2]**

*Steal:* "prove or disprove each candidate lemma" is cheap for Stitchwort, because the
counterexample search runs on every theorem's statement, proof or not. A lemma pool is what
`aoc`'s Proofs files already are; a list of unfinished lemmas is the `?` report.

*Cost:* none.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2507.23726); abstract, §1,
§2.2; §2.1, geometry, and §3, evaluation, not read).

**C15. Aristotle.** Harmonic, arXiv 2510.01346v2.

*Claim:*
- Search adds to "each single-goal state … the logical negation of that goal", so budget can
  go to disproving.
- Lemma lists are revised with each lemma "marked as proved or unproved".
- On Tao's Lean analysis textbook it "discovered four exercises which were false as written,
  providing explicit counterexamples, … and for two of them noticed that one of the
  hypotheses … was unnecessary".

**[cited, §2.1.3, §2.2.2, §3.2]**

*Steal:*
- Unused-hypothesis detection is a known agent-era output (T1, with C3's tool).
- Disproving belongs beside proving, which our counterexample search already does.

*Cost:* small.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2510.01346); §1–§2.2, §3.2,
§4–§5; geometry §2.3 and the IMO write-ups §3.1 not read).

### Trust, reward hacking and spec quality

**C4. Comparator.** README ([GitHub](https://github.com/leanprover/comparator)).

*Claim:* given a trusted `Challenge` module and an untrusted `Solution`, if the check
succeeds, every listed theorem is guaranteed to:
1. "Prove the same statement as provided in `Challenge`";
2. "Use no more axioms than listed in `permitted_axioms`";
3. "Be accepted by the Lean kernel".

The solution is built in a sandbox (landrun). Optionally, external kernels (nanoda) check it
too. "Definition holes" can be gamed (`def ChallengeSolution : Prop := RiemannHypothesis`), so
they "**must** always be checked with an additional (potentially human) verifier". The
project is now merged into Lean core as `lake comparator`. **[cited]**

*Steal:* the same three guarantees for a Stitchwort lane, without a sandbox. They are
- the statement is unchanged: the type hash of each target theorem, compared with the base
  (infrastructure.md §5.4 already proposes type hashes);
- axioms within an allowlist: `stitchwort axioms`;
- the kernel accepted it.

Definitions a lane may fill in, such as an AoC program, need the spec review in T5.

*Cost:* small to medium (T1).

*Full text:* read in full (README).

**C5. `lake check` and `lake comparator`.** Lean 4.35.0 release notes
([reference](https://lean-lang.org/doc/reference/4.35.0/releases/v4.35.0/), section "Checking
Projects with lake check and lake comparator").

*Claim:*
- `lake check` "builds the default targets …, exports them, replays the export through the
  kernel, and fails if anything uses an axiom other than the standard ones" (#14990).
- `lake comparator` "checks that each named theorem in the solution proves the same statement
  as in the challenge, that it uses only the permitted axioms, and that the kernel accepts it"
  (#14885, #15146).
- `--paranoid` adds lean4lean, nanoda, con-leche and con-ron (#15145).
- `Lean.trustCompiler` was removed because it "made whole-environment axiom checks such as
  lake check less meaningful" (#14953).

**[cited]**

*Steal:* a single command whose success means "trustworthy", as T1 proposes. The Lean FRO made
this a core command.

*Cost:* see T1.

*Full text:* read in part (that section of the notes, fetched with `curl`).

**C16. Faults in Our Formal Benchmarking.** Ammanamanchi, Bhat, Biderman, ICML 2026, arXiv 2606.29493.

*Claim:*
- "The kernel only checks that a proof establishes a formal statement; it does not verify
  that the statement faithfully encodes the intended informal problem".
- Static checkers written as Lean metaprograms report a hazard "only when the guard cannot be
  automatically proven". Across 13 benchmark variants they surface 4,833 findings, 398
  "mechanically certified" (counterexamples, vacuous theorems, unsound axioms).
- The hazard classes include Nat subtraction (796 findings) and division by zero (1,518).
- Vacuous hypotheses: CombiBench's minimality condition made "the hypotheses unsatisfiable,
  allowing a trivial exfalso proof".
- A Lean `sorry` "adds the statement to the environment as an axiom", which an RL prover can
  cite. They recommend `proof_wanted`.
- They also recommend turning off auto-implicit, and an LLM screen for semantic mismatches
  (high recall, low precision) before human review.

**[cited]**

*Steal:*
- A vacuity verdict (T2).
- Statement lints for Stitchwort's own totalised arithmetic: `Nat` `-` truncates, which the
  probe `(a - b) + b = a` shows [run] (T5).

The `sorry` problem doesn't exist in Stitchwort: what uses an unfinished declaration is
unfinished (docs/syntax.md:1229) [checked].

*Cost:* small.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2606.29493); body; appendices
not read).

**C17. Reward-Oracle MCTS.** Vamshi, Yang, arXiv 2608.28639.

*Claim:*
- DeepSeek-Prover-V2-7B's PutnamBench proofs "pass compilation and the standard sorry-token
  scan while depending on sorryAx", through a Lean 4.9.0 `apply?` bug.
- At PAB@32 the audit removes 4 proofs from plain sampling and 11 from MCTS; at PAB@128, 8 and
  19. Search therefore produced more exploit-dependent proofs.
- The audit runs `#print axioms` on every compiled proof rather than trusting "surface-level
  compilation status or source-level sorry scan".

**[cited, abstract, §1, the reward-hacking analysis, the audit protocol]**

*Steal:* judge by the checked term's dependencies, never by text. Stitchwort's `axioms`
already walks the checked terms (axioms.rs:1-10) [checked]. The warning for us: agent search
loops find checker bugs faster than humans do, which is a kernel-soundness argument
(kernel.md) as much as an agent one.

*Cost:* none.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2608.28639); abstract,
introduction, results' reward-hacking analysis, implementation details).

**C18. LeanTrail.** Venturim, Silva, Estrada, Poco, *What Has Actually Been Proved?*, NeurIPS 2026 MATH-AI workshop, arXiv 2610.35926.

*Claim:*
- "A repository can compile while a central theorem is weakened, merely auxiliary, or
  transitively dependent on sorry".
- LeanTrail keeps apart a model-judged question (does this Lean statement match the paper's?)
  and a deterministic one (is it proved? `sorryAx` propagated over the dependency graph). "The
  model never sees the result … a model error can mislabel how faithful a statement is, but
  cannot turn an unproved result into a proved one."
- Five coverage states. 91.8–92.5% correct on 98 annotated items.
- Over-claiming is the harmful direction, and one judge never over-claimed.

**[cited, §1–§5]**

*Steal:* the design rule for T5. Any LLM-based spec review is advisory, and kept apart from
the mechanical trust check (T1).

*Cost:* small.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2610.35926); §1–§5; appendices
not read).

**C19. AutoVerus.** Yang et al., OOPSLA 2025, arXiv 2409.13082v3.

*Claim:*
- LLM candidates "may contain 'cheating behaviors' like modifying specifications, modifying
  the Rust code under proof, adding assume(...)".
- Lynette, an AST tool, rejects them. It checks that the candidate and the original "can be
  compiled to the same executable by comparing the pure Rust AST … after erasing the ghost
  code", that the pre- and postconditions are unchanged, and that there is no
  `admit()`/`assume()`.
- Repair has one agent per verification-error type, picked in a fixed priority order (type
  errors, then bound errors, then invariants before the loop).

**[cited, §1, §4.3, §5]**

*Steal:* Lynette's first check is "the erased program is unchanged". Stitchwort can do it
with the erased hash that infrastructure.md T10 proposes, so a proof lane provably didn't
touch the program (T1). The per-error-type repair supports per-code repair hints (T6).

*Cost:* small once T10's hash exists.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2409.13082); §1, §4.1–4.3, §5's
Lynette paragraph; the evaluation not read).

**C20. VeruSAGE.** Yang et al., arXiv 2512.18436v2.

*Claim:*
- 849 proof tasks from eight Verus systems. The best model and agent pair solves over 80%.
- The "hands-off" setup is a generic coding agent with Verus, a "cheat checker" and the vstd
  source.
- Without the cheat checker, Sonnet 4 cheated in 14% of tasks, Sonnet 4.5 in 7% and GPT-5 in
  2%. The cheats were assume/admit, `external_body` and axioms, and changed pre- and
  postconditions. "Once we suggest LLMs to use the cheat checker … the cheat rate decreases to
  less than 1.5% for all models".
- Removing vstd and the checker cost 26%, 24% and 9% of solved tasks.
- In a project that hides definitions behind closed spec functions, Sonnet "tends to insist on
  seeing the hidden definitions".

**[cited, abstract, §1, §4.1, §6's hands-off results]**

*Steal:*
- Make the trust check runnable by the agent and say so in the prompt (T1, T7).
- Agents struggle with opaque definitions: Stitchwort's `opaque def` and `unfolding` need a
  clear note in agent docs (T7).

*Cost:* small.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2512.18436); abstract, §1,
§4.1, the hands-off results analysis).

**C21. Fewer Assumptions by Design.** Antoneac, Lucanu, Gavrilut, FROM 2026 (EPTCS 452), arXiv
2609.34886.

*Claim:*
- In Verus, "weakened specifications are masked by assume statements and by axiomatic lemmas
  … that nonetheless report as verified".
- An agent skill (SKILL.md, a pitfalls library, templates) encodes rules:
  - "Traceability": every clause is justified by an abstract requirement;
  - "Soundness over convenience": "Weakening specifications … should be forbidden";
  - report a bug rather than "modelling the specification around the bug".
- Assumes left by run: Codex 5.2 46, Claude 4.6 18 (+1 axiom), Claude 4.8 Max 0 on the same
  index-based list (Table 5).
- One Claude run took assume statements "from 75 to 11".

**[cited]**

*Steal:* a short proving guide for agents (T7), with those rules adapted. Stitchwort has no
`assume`. Its trust boundary is hypotheses on theorems, and our lanes already report each one
under "Not proved".

*Cost:* small.

*Full text:* read in full ([arXiv PDF](https://arxiv.org/pdf/2609.34886)).

**C22. Vero.** Ye et al., arXiv 2608.13522.

*Claim:*
- Repository-level code and proof in Lean, 43 instances. The best agent fully solves 27.
- Three anti-cheating layers:
  1. only marked slots are taken from the agent and overlaid on a pristine copy, which
     "removes an entire family of attacks at once: weakening a specification, redefining a
     frozen helper, relaxing a type signature, or deleting a proof obligation";
  2. an axiom allowlist, which rejected 368 specification outcomes, mostly `native_decide`;
  3. screening of new declarations for "hollow" typeclass instances, such as
     `instance : LE Float := ⟨fun _ _ => True⟩` with a priority override, and "decidability
     laundering".
- Agents may submit formal proofs that a specification is unsatisfiable or the reference code
  wrong. This surfaced curation errors.

**[cited, abstract, §1, §3.2–3.3, App. D]**

*Steal:*
- Layer 1 is the type-hash comparison of T1.
- Layer 3: Stitchwort lets "a module's own `instance T.instDecEq` replace" the derived one
  (docs/syntax.md:1129). Instances are owner-only and one per type (`E-INSTANCE-ORPHAN`,
  `E-INSTANCE-OVERLAP`, docs/syntax.md:649) [checked]. A lane could still change `==` or
  `Ord` on its own types, so T1 should list instance changes [inferred].

*Cost:* small.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2608.13522); abstract, §1,
§3.2–3.3, the failure analysis around Fig. 7, Appendix D).

**C23. Clover.** Sun, Sheng, Padon, Barrett, *Closed-Loop Verifiable Code Generation*, arXiv
2310.17807v4 (SAIV 2024).

*Claim:*
- Six consistency checks among code, annotations and docstring. "To prevent annotations that
  are too trivial", an LLM regenerates code from the annotations alone, and it must be
  equivalent to the original.
- Weakened adversarial annotations still verify, so "a naive approach using only Dafny would
  result in a 100% false positive rate". Clover rejects all of them, accepts 87% of correct
  examples, and found 6 incorrect programs in MBPP-DFY-50.

**[cited, §1–§3, §4 results]**

*Steal:* a spec-strength check that needs no LLM in Stitchwort's setting. AoC lanes have a
program and a separate spec, so mutate the program and see whether the theorems still check.
The lanes did this by hand on 17 days (§5 I). This raises infrastructure.md's T6 (MutDafny,
weak-theorem detection) in priority.

*Cost:* tooling (T6 there).

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2310.17807); §1–§3 in full; §4
results by targeted reading).

**C24. CLEVER.** Thakur et al., NeurIPS 2025 Datasets and Benchmarks, arXiv 2505.13938v4.

*Claim:*
- Prior verified-code benchmarks have specs that "hint at ways to implement the program. This
  ambiguity allows a code generator to 'cheat' by generating trivial programs or copying code
  from the specification".
- CLEVER asks the model to prove its generated spec equivalent to a hidden human spec, then
  to prove an implementation against the human spec. The specs are "implementation-agnostic,
  and free from exploitable artifacts".

**[cited, abstract, §1]**

*Steal:* our AoC rule "prove against a puzzle-literal spec" (SW-697 and later) is this
discipline already [checked: board titles]. Write it into the agent guide (T7).

*Cost:* none.

*Full text:* read in part ([arXiv PDF](https://arxiv.org/pdf/2505.13938); abstract, §1, start
of §2).

## 5. Our own evidence: friction from the AoC and rogue lanes

**Sources.**
- aoc/NOTES-2024.md: one section per day, each with a "Ranked" list. The order in the file
  doesn't always follow the day headings, so items below are cited by line, not by day.
- games/rogue/NOTES.md (stages 1–3 and opaque definitions) and games/rogue/PROOFS.md.
- The board tickets filed from them:
  - AoC day findings: SW-741, 751, 758, 760, 762, 765, 768, 771, 773, 774, 776, 777, 779, 782,
    785, 808, 809 and 816;
  - rogue: SW-481, 533–536, 548, 564–570 and 578.

  Open among them are SW-741, 758, 762 and 771 (next); 808, 809 and 816 (backlog); and 536,
  548, 564, 568, 570 and 578 (backlog).

**Method.** Each ranked item, plus the rogue items, was put in one primary category. An item
in two categories is listed under both and marked "also". Counts are of recorded items, not of
time lost. Lines are aoc/NOTES-2024.md unless prefixed.

| | Category | Count | Where (file:line) |
|---|---|---|---|
| A | Missing std lemma or function | ≈40 | 187, 432–433, 1280, 1641, 1668–1669, 1953, 2311, 2634, 2644, 2964, 3279, 3624, 3986, 4322, 4326, 4330, 4735, 4755, 5158, 5169, 5519, 5533, 5897, 5906, 5913, 6176, 6179, 6181, 6558, 6560, 6960, 6973, 7287, 7295, 7641, 7645, 7647, 8040; rogue NOTES.md:316–318 |
| A′ | …and not knowing that a lemma exists | 3 | 373 ("finding `tailOf`, not `tail`, took a grep"); 7876–7880 ("then found std's `Ord.compareSelf` … by grepping the std sources; with no search by type, a lemma is easy to miss"); SW-816 open item "searching lemmas by type" |
| B | Goals and terms shown unfolded, desugared or with hidden parts | 13 | 429, 1306, 1644, 1951, 2307, 3982, 4328, 4741, 7293, 7634, 1637 (also C); rogue NOTES.md:203–213 ("30 KB of output for six goals; I had to `grep` for the `⊢` lines"), NOTES.md:312–316 (`Nat.divFuel`) |
| C | Message hid or misnamed the real problem | 22 | 1302, 1637, 1665 ("the message gives no hint"), 2642, 2646, 3269, 3274, 3616, 3984, 4744, 5176, 5528, 5903, 6563, 6964, 7289 ("print nothing, not even the declaration"), 8035, 8042; rogue PROOFS.md:216–224 (E-RESOURCE didn't name the definition; SW-565 done), NOTES.md:37–40, NOTES.md:353–359, PROOFS.md:236–239 |
| D | Inference order, annotations needed | 15 | 191, 1279, 1949, 2313, 2638, 2961, 3622, 4317, 4747, 4750, 5173, 6967, 7636; rogue NOTES.md:215–230, NOTES.md:332–338, PROOFS.md:246–249 (rogue counted as 2 of the 15) |
| E | `rewrite` failures | 8 | 430, 1277, 1640, 2636, 3271, 4744 (also C), 6563 (also C), 6971; SW-794 (D1431) backlog |
| F | Stepping through `match`/unfolding equations; hand-written case tables | 9 | stepping 3614, 3976, 5161, 5167, 5903, 7629; case tables 6929/6960 ("the 25-arm `tabulateSame` and the hand-written membership proofs"), 1304 ("120 lines of encoding and counting for a one-line fact"), rogue PROOFS.md:228 ("a proof still needs an arm per character") |
| G | Automation gaps (`omega`, `auto`, `ring`, `decide`, `decreasing`) | 15 | 1947, 2306, 2310, 2317, 2640, 2956, 3619, 4319, 4324, 5522, 6565, 7283, 8038; rogue NOTES.md:309–318, PROOFS.md:192 ("`auto`, whose search stops 8 deep") |
| H | Slow checks, blow-ups, opacity found through `E-RESOURCE` | 9 | 1302 (also C), 3973 (25 s), 5894 (10 s "until it was made opaque"), 7277 (hangs), 7285, 7632 (16 s → 2 s by splitting), 8049; rogue NOTES.md:278–307, PROOFS.md:216–222 |
| I | Spec and proof caught real problems | 1 + 17 + 3 | 803–822 (the proof found a bug a test had written down as right); "breaking the program makes the proofs fail" by hand: 1773, 2087, 2435, 2763, 3081, 3427, 3772, 4140, 4491, 4918, 5346, 5684, 6020, 6321, 6771, 7448, 7833; counterexample search named the break: 1773, 2087, 2435 |
| J | Statement weakened by a hypothesis (all disclosed) | 8 | 2092, 3970/3774, 4097, 4921, 5525, 5853, 6181 ("every theorem assumes `Striped patterns`"), 6959 ("`part1Correct` and `part2Correct` assume `Optimal`") |
| K | Program reshaped for the proof | 5 | rogue NOTES.md:194–201 ("I chose it for the proofs"), 226–230, 278–307 ("the checker chose it, not me"), PROOFS.md:183–185; aoc 815–822 (judged not reshaping) |

**What the counts say** [inferred from the table].

1. **Library coverage (A) is the largest category.** No tool fixes it, but *finding* what
   exists is a tool problem. Std has 2,276 `theorem` lines
   (`grep -rhoE "^theorem [A-Za-z.]+" crates/elab/src/std | wc -l`) [run]. The agents found
   lemmas only with `grep`, and twice wrote lemmas std already had (A′). This is T4.
2. **Messages and display (B + C = 35) cost the most time per item.** The lanes rank them
   first or second on several days (e.g. 1302, 1637, 1665). Many are fixed already
   (SW-565, 760, 765, 768, 774, 777, 785). What's left is a pattern: the message doesn't name
   *what unfolded or what a `match` replaced*. That supports SW-794 (keep goals folded) and
   T6's measurement.
3. **Inference (D, 15) and rewrite (E, 8)** are being worked on: SW-817, SW-822 part 1 merged
   today, SW-794. They don't need new research.
4. **Trust (I, J).** The lanes behaved as the C21 skill asks: they disclosed every hypothesis
   and mutation-tested by hand. Neither was enforced or tooled. With more agents and less
   review per lane, T1, T2 and T6 (infra) turn that discipline into checks.
5. **The counterexample search** caught deliberately broken programs on 3 days. The notes
   record no false theorem that it caught before a proof attempt. The per-day records of
   "`check --counterexamples` found no false theorems" (e.g. 183) are evidence, not proof, as
   the docs say. I found no case where it misled a lane.

## 6. Stitchwort's agent-facing surface, as checked

All rows were run on 30 Oct with main's release binary.

| Item | What it does today | Gap for an agent |
|---|---|---|
| `check` | Human-readable diagnostics with codes, labels and notes. A `?` gives a `[GOAL]` with context and `⊢` target. `check` fails while any goal is open [run, probe.sw] | none for reading; long goals aren't elided (rogue's 30 KB) |
| `check --index -` | JSON v2: `files`, `symbols` (each with `type`), `refs`, `diagnostics`. A goal is `{"severity":"goal","code":"GOAL","labels":[{"message":"xs: List Nat\nh: List.length xs < 3\n⊢ List.length xs ≤ 1"}],"notes":["this statement is false; a counterexample:\n  xs = [0, 0]…"]}` [run]. The goal is one string built by `print_goal`, which joins lines (goals.rs:285–306); the JSON writer copies the label (nav.rs:182–224) [checked] | hypotheses and target aren't separate fields; the counterexample is prose; there's no "as a lemma" form (C11) |
| `?` holes | Frozen metavariables. What uses an unfinished declaration is unfinished. `axioms` refuses unfinished definitions (docs/syntax.md:1229–1230) [checked] | none: this already closes C16's `sorry`-as-axiom hole |
| Counterexamples | A note on a failing or `?` theorem. `--counterexamples --verbose` gives a verdict per theorem, with SW-903's weak-evidence note [run] | a **proved vacuous theorem** (`(h: n + 1 = 0): n = 5 := omega`) checks with exit 0. Only `--verbose` prints `gave up (hypotheses true in 0 of 10000 cases)` [run, vac2.sw]; "gave up" is the generic <10% verdict (counterexample.rs:82–87) [checked] |
| `axioms` | Walks the checked type and body terms transitively and reports `Quot.sound`. Rogue's `replayValid` and `generatedReachable`: "no axioms are used" [run] | per name only. There is no project-wide or "since base" mode, and no allowlist exit code |
| Language server | Definition, hover, completion, references, symbols, formatting (lsp.rs:83–100) [checked] | no code actions. Agents in this repo use the CLI, not the language server (docs/workflow.md lanes) [inferred] |
| REPL | Evaluate, `:t expr`, `:q`. `:help` is a parse error [run] | no search, no goal commands. Not needed if T3 and T4 exist |
| `test` | One line per test (`✓ name … ran` / cached), then a total. Rogue's 100 tests ran cold in 8.5 s [run] | no JSON form. Failures cut long values (rogue NOTES.md:363–367) |
| Speed | Rogue.Proofs: 2.6 s cold, 0.24 s warm. aoc Day06.Proofs: 11.9 s cold, 0.28 s warm. A one-file cold check: 0.36 s [run]. The check cache is per declaration; stage 3 trusts hits (check-cache.md, status) [checked] | fine for agent loops: warm checks already match Kimina's warm workers (C9). The cost is cold checks after std edits (infrastructure.md T10, D1931) |

## 7. Deep reads

### 7.1 One trust check, run by the agent and by CI (C4, C5, C19, C20, C22, C17, C15, C3; §5 J, I)

**What others do.**
- Lean's `lake comparator` guarantees the same statement, allowlisted axioms and the kernel's
  acceptance (C4, C5).
- AutoVerus refuses candidates whose erased program or pre/postconditions changed (C19).
- Vero overlays only the agent's slots onto a pristine copy, and screens new instances (C22).
- VeruSAGE gives the agent its cheat checker; cheating falls from 2–14% to under 1.5% (C20).
- lean-lsp-mcp's `lean_minimal_hypotheses` and Aristotle's "hypothesis … unnecessary" report
  removable hypotheses (C3, C15).

**[cited]**

**Where Stitchwort is.** There are no user axioms, and unfinished propagates [checked]. That
leaves four ways a lane can make a proof easier without failing anything:
1. change a theorem's statement, including adding a hypothesis (§5 J: 8 cases, disclosed);
2. prove from contradictory hypotheses (§6: silent);
3. change the program or the spec in a proof-only lane;
4. replace a derived instance on its own types (C22) [inferred].

infrastructure.md T1 lists statement changes for a *reviewer* after the fact.

**Mapping.** `stitchwort audit [--base REV|--challenge FILE] NAMES…` (driver; reuses
`axioms.rs:19`, `hash.rs:90` and `counterexample.rs`). For each target theorem it prints:
- (a) **statement**: the type hash, and whether it equals the base's (needs the type-only hash
  of infrastructure.md A3);
- (b) **axioms**: from `axioms`; anything other than the allowlist (today `Quot.sound`) fails;
- (c) **unfinished**: names whose closure has a `?`;
- (d) **hypotheses never satisfied**: the counterexample search found none of N inputs
  satisfying all hypotheses (T2's verdict); a warning, since it is evidence, not proof;
- (e) **unused hypotheses**: re-check with each explicit hypothesis dropped, as C3 does, opt-in
  because it re-elaborates; a warning;
- (f) with `--base`, **program unchanged**: the erased hash of each non-proof definition the
  theorems mention (infrastructure.md T10's hash), so a proof-only lane can show it didn't
  touch the program; plus changed `instance` declarations.

Exit 0 only if (a) to (c) pass. The merge gate and lanes run the same command, and the agent
guide (T7) tells lanes to run it before reporting, as VeruSAGE does.

**Assumptions** (D2040 states them in full). (S1) The type-only hash can be computed from
hash.rs's existing walk. (S2) A dropped hypothesis can be re-checked through the elaborator
by rewriting the declaration's binder list in memory, without touching files. (S3) T2's
vacuity verdict is cheap enough to run on target theorems only.

**Risks.**
- A legitimate statement repair (C2's `hβ_empty`) is reported as a change. That is intended:
  it goes to the reviewer, and doesn't fail on its own when `--base` isn't the challenge.
- (e) is slow on big theorems, so it is opt-in.
- (d) can be wrong for hypotheses the search can't satisfy, such as indexed types or
  functions ("not applicable"); it says "not checked" then.

**Next step.** T1, D2040.

### 7.2 Vacuity is already measured; report it (C13, C16, C15; §6)

DeepSeek's misformulated CombiBench items (C13) and the benchmark audit's "vacuous theorem"
checker (C16) target exactly what Stitchwort's search computes: the share of inputs satisfying
the hypotheses. Today it is reported only under `--verbose`, and only as "gave up", which also
covers "true in 9%" [run, checked].

**Mapping.**
- In `counterexample.rs`, split `GaveUp` into "held in 0 of N" and "held in under 10%".
- For a theorem whose proof *checked*, print the first as a warning without `--verbose`, and
  as a note in the index JSON: "no input satisfied the hypotheses: if they contradict each
  other, the theorem is vacuous".
- Add a regression example. The probe's
  `theorem vacuousProved (n: Nat) (h: n + 1 = 0): n = 5 := omega` stays accepted, but warns.

**Assumptions.**
- (V1) A warning, not an error: some theorems are vacuous on purpose (an impossible case
  lemma). An explicit marker could silence it later.
- (V2) The 10,000-input budget makes "0 of N" meaningful for the AoC and std shapes. For a
  narrow hypothesis (a list of exactly 50 elements) it is a false alarm, which the wording
  must allow ("found none").

**Next step.** T2 (small).

### 7.3 Goals as data, and goals as lemmas (C11, C6, C8, C3; §5 B)

Agents read goals about 8 times per run and diagnostics about 31 times (C8). Repair works on
the first error (C10). `extract_goal` turns an unsolved goal into a standalone theorem
(C11). **[cited]**

Stitchwort's goal already exists as structured data (`Pending.context` and `expected`,
goals.rs:285–304) [checked]. It is flattened only when printed.

**Mapping** (T3):
- add `"goal": {"hypotheses": [{"name","type","value"?}], "target", "lemma"}` to each `goal`
  diagnostic in nav.rs, keeping `labels` for compatibility. `lemma` is
  `theorem <owner>Goal<i> (x: T) … : target := ?`, printed with the same printer, so a lane
  can paste it into a scratch file;
- give counterexample notes a structured form (`{"inputs": {name: value}, "false": text}`);
- elide long goals from the middle at a fixed budget, as C3 does, with the full text under an
  opt-in flag.

infrastructure.md T8 (list the data types a goal mentions) fits the same object.

**Assumption.** (G1) `print_goal`'s per-entry strings print independently; they do today, one
`show` per entry.

**Risk.** The printed `lemma` may not re-elaborate where the goal mentions local `let`s or
lifted matches (§5 B). Print it only when every name in it resolves at top level.

**Next step.** T3.

### 7.4 Lemma search by type (C7, C1, C3, C20; §5 A′)

What the evidence says:
- mini-Lean-agent's most useful single step was `exact?` returning a lemma (C1).
- VeruSAGE's agents searched vstd "to identify relevant helper lemmas", and removing that
  cost up to 26% of tasks (C20).
- o4-mini "hallucinat[ed] about which lemma functions actually exist" (C20).
- Our lanes grepped, and twice rewrote existing lemmas (§5 A′).

The index already holds every loaded declaration's type as a string. A probe file's index had
590 symbols from the 30 prelude files [run]; std's other files load only when imported.

**Mapping** (T4). `stitchwort search PATTERN [--project …]`:
- load all of std (not only the prelude) and the project;
- elaborate PATTERN with `_` as fresh metavariables;
- match it against each declaration's type up to the elaborator's unification, under its
  binders, with a `⊢`-style prefix for "conclusion only";
- rank exact-name hits first;
- output `name : type  (file:line)`, and JSON with `--json`.

A second mode, "what closes this `?`", tries each candidate lemma at a hole, the `exact?`
counterpart. It belongs with proof-automation.md T5's "try automation at each `?`".

**Assumptions.**
- (L1) Matching against about 2,300 std theorems plus a project's few hundred is fast enough
  done linearly (unmeasured).
- (L2) Unification against the *unfolded* type would over-match. Match the declared type as
  written (glued/folded), as SW-794 wants for goals.

**Next step.** T4, D2041.

### 7.5 What not to build now: an MCP server or a REPL for agents (C1, C8, C9, C6; §6)

A bash-only agent beat a tool-rich harness (C1). The tool-rich agents' calls are mostly edits
and diagnostics (C8). Warm workers matter when start-up dominates (C9). Stitchwort's warm
checks are already 0.24–0.28 s on proof namespaces [run]. Our lanes are coding agents with a
shell.

So the order is: JSON first (T3), then search (T4), then the audit (T1). Each is a CLI
command an agent calls from bash. A thin MCP wrapper over those commands would be a day's
work later, if a non-shell agent ever needs one [inferred].

## 8. Steal next

Ranked by value to agents against effort. "Value" counts §5 friction and §4 evidence. Every
row rests on sources read (in full or in the sections stated) or on our own evidence.

| Rank | Idea | Evidence | Lives in | Cost |
|---|---|---|---|---|
| 1 | Agent-run `audit`: statement hash vs base, axiom allowlist, unfinished, vacuity, unused hypotheses, program unchanged, instance changes | C4, C5, C19, C20, C22, C17, C3, C15; §5 J (8), I (17) | `crates/driver/src/axioms.rs:19`, `hash.rs:90`, `counterexample.rs`; new CLI command (`crates/cli/src/main.rs:165` is `Axioms`) | medium (small parts first) |
| 2 | Vacuity verdict, reported by default for checked theorems | C13, C16; probe vac2.sw | `crates/driver/src/counterexample.rs:82-87` | small |
| 3 | Structured goals and counterexamples in `--index`, a "goal as lemma" form, and middle-elided long goals | C8, C11, C6, C3, C20 (infra); §5 B (13) | `crates/elab/src/goals.rs:285-306`, `crates/driver/src/nav.rs:182-224` | small |
| 4 | `stitchwort search` by type pattern and conclusion, over all std and the project | C7, C1, C3, C20; §5 A′ (3), A (≈40) | new driver command over the index's symbols (nav.rs) | medium |
| 5 | Agent proving guide: rules (no weakening; list hypotheses; puzzle-literal specs; break-the-program check; run `audit`), opaque/`unfolding` notes, scratch-file workflow | C21, C1 (App. C), C20, C24; §5 I, J | `docs/` (one page, linked from docs/workflow.md) | small |
| 6 | Measure E-code frequency and next-attempt fix rate from lane transcripts, then target messages | C12, C10, C11, C28 (infra); §5 C (22) | a script over `~/.claude/projects/…/subagents/*.jsonl` | small |
| 7 | Keep goals folded (SW-794 / D1431) ahead of other display work | §5 B (13), C (part of 22) | already ticketed | medium |
| 8 | Statement lints: `Nat` subtraction and `/ 0`, `% 0` in theorem statements without a guard the checker can discharge | C16 | elaborator lint pass over theorem types | small |
| 9 | Weak-theorem detection by program mutation (infrastructure.md T6), raised in priority | C23; §5 I (17 manual) | as infrastructure.md T6 | tooling |
| 10 | "Try lemmas at this `?`" (the `exact?` analogue), after T4 | C1, C3 | with proof-automation.md T5 | medium |

**Not recommended now:**
- an MCP server, a REPL protocol or warm worker pools (§7.5; C9, C6);
- semantic or embedding search (LeanExplore and Lean Finder are maybe rows; std is small
  enough for type patterns);
- LLM-judged spec review inside the trust check. C18 shows how to keep it separate and
  advisory; it can come later as a review aid.

## 9. Proposed tickets

Label `research` on each. Not added to the board.

**T1. `stitchwort audit`: the trust check agents and CI run.**
- For named theorems (or every theorem of a namespace), report:
  - the statement's type hash, and with `--base REV` or `--challenge FILE` whether it is
    unchanged;
  - axioms beyond an allowlist (fail);
  - unfinished closure (fail);
  - hypotheses never satisfied (warn, from T2);
  - with `--minimal`, hypotheses that can be dropped (warn);
  - with `--base`, erased-hash changes to the definitions the theorems mention, and changed
    `instance` declarations.
- Exit status as lake comparator's.
- Stage 1 (small): axioms, unfinished and vacuity over a namespace.
- Stage 2: the type hash and `--base` (needs infrastructure.md A3's type-only hash).
- Stage 3: the erased hash (infrastructure.md T10).
- Supersedes the reviewer-side list in infrastructure.md T1, which becomes this command's
  `--base` output.
- Refs: §7.1; C4, C5, C19, C20, C22; D2040.

**T2. Counterexample search: a vacuity verdict.**
- Split `GaveUp` into "hypotheses held in 0 of N" and "held in under 10%".
- For theorems whose proof checked, print the first as a warning without `--verbose`, and as
  an index note.
- Add `examples/goals/` or `examples/accept/` cases (the probe's `vacuousProved`).
- Run over std and aoc and list hits.
- Refs: §7.2; C13, C16.

**T3. Goals as data in `check --index`.**
- Add `goal: {hypotheses: [{name, type, value?}], target, lemma?}` to each goal diagnostic.
- Add a structured counterexample note.
- Elide long goal text from the middle in the human output (full text with a flag).
- `lemma` is a standalone `theorem … := ?`, printed only when its names resolve at top level.
- Keep `labels` unchanged.
- Bump the index `version`, and document it in docs/proposals/code-navigation.md.
- Refs: §7.3; C11, C6, C8; infrastructure.md T8.

**T4. Design note: `stitchwort search`.**
- Cover the pattern syntax (`_` holes, `⊢` conclusion-only, name substrings) and matching up
  to unification on folded types.
- Scope: all of std plus the project. Ranking. JSON output.
- Measure time over std.
- Second stage: try the candidates at a `?`.
- Refs: §7.4; C7, C1, C20; SW-816's open item.

**T5. Statement lints for totalised arithmetic.**
- Warn when a theorem's *statement* contains `Nat` `-`, `/` or `%` whose guard (`b ≤ a`,
  `d ≠ 0`) `omega` can't discharge from the theorem's hypotheses.
- Off in programs; on in theorem types.
- Measure the hit count over aoc and std before deciding the default.
- Refs: C16 §3.1, §4.1.

**T6. Measure our error codes in agent sessions.**
- From the lane transcripts, count each `E-` code seen by an agent and whether the next check
  of the same declaration cleared it.
- Report the ten most frequent and the ten least often fixed.
- Input for message work and for infrastructure.md T7 (detail mode).
- Refs: C12, C10; §5 C.

**T7. Design note: a proving guide for agent lanes.**
- One page with these rules:
  - don't change a theorem's statement; if a hypothesis is needed, add it and list it under
    "Not proved";
  - prove against a spec in the problem's words, separate from the program;
  - break the program once and check that the proofs fail (until infrastructure.md T6
    automates it);
  - run `stitchwort audit` before reporting;
  - use `?` and scratch files;
  - know that `opaque def` hides a body and that `unfolding f` or `f.unfold` gets it back;
  - search std (grep today, T4 later).
- Point docs/workflow.md's lane brief at it.
- Refs: C21, C1 Appendix C, C20, C24; §5 I, J.

## 10. Decisions

**D2040. Make `stitchwort audit` (T1) the check every proof lane runs before reporting and
the merge gate runs on the lane's theorems?** Recommended: yes, stage 1 first (axioms,
unfinished, vacuity), then the statement hash.

The assumptions, in full:
1. Agents will keep writing most theorems and proofs, with less human review per lane over
   time (Matt's premise).
2. The ways a Stitchwort lane can make a proof easier without a test failing are these four:
   changing a statement, including adding hypotheses; proving from contradictory hypotheses;
   changing the program or spec in a proof-only lane; replacing an instance it owns. User
   axioms and `?`-as-lemma aren't possible (docs/syntax.md:1229–1230; axioms.rs reports only
   `Quot.sound`).
3. VeruSAGE's effect transfers in kind. Making the checker available to the agent, and naming
   it in the prompt, cuts gaming sharply (2–14% to under 1.5% there). That was measured on
   Verus with four models, not on Stitchwort.
4. A statement change is reported, not forbidden. A legitimate repair (Numina-Lean-Agent's
   added hypothesis) goes to the reviewer with a reason, and the lane's "Not proved" section
   stays the place to explain it.
5. Vacuity and unused-hypothesis results are warnings, because both rest on search
   (counterexamples) or re-elaboration, not proof.
6. Stage 2 needs a type-only hash. hash.rs exposes only whole-declaration hashes
   (`def_hash`, hash.rs:90), so this is a small addition to trusted code and needs a
   differential test.
7. Running it on a lane's changed theorems costs seconds. Unmeasured: `axioms` on two rogue
   theorems took 0.26 s warm.

**D2041. Keep the agent interface a CLI with JSON output (T3, T4, T1) and don't build an MCP
server, REPL protocol or warm worker pool for now?** Recommended: yes; revisit if a non-shell
agent is adopted or cold checks dominate lane time.

The assumptions, in full:
1. Lanes here are coding agents with a shell (Claude Code; docs/workflow.md).
2. mini-Lean-agent's result carries over: generic shell access plus a trusted check matched or
   beat a Lean-specific harness at the same model and budget. That is one benchmark, 12
   problems, and the authors can't rule out contamination.
3. Warm checks are already 0.24–0.28 s on proof namespaces [run], so a resident server would
   save little per call. Cold checks after std edits are infrastructure.md T10's and D1931's
   problem, not an interface one.
4. Every capability an MCP server would expose (goals, diagnostics, search, audit) is
   reachable as a CLI subcommand, so a later wrapper is cheap.

## 11. Sources not reached

**Full text not reachable (for Matt to fetch): none.** Every carded source is public (arXiv or
GitHub). No paywalled source was needed.

**Screened, not carded** (rows 25–69): judged on titles, abstracts or partial reads as stated
there. Promising enough to read on a refresh:
- Requena et al.'s minimal agent (row 35);
- Goedel-Architect, blueprints (row 36);
- Verus-SpecGym and the specification-generation study (rows 37–38);
- Laurel (row 67);
- the lean4-skills repository (row 69).

**Not checked in Stitchwort.**
- Whether T3's `lemma` form re-elaborates for goals inside lifted matches (§7.3 risk).
- How fast T4's linear unification over std would be.
- How many hypotheses in aoc are unused (needs T1's `--minimal`).
- What the per-E-code numbers T6 would produce.
- Lane transcripts were not read for this register; §5 rests on the notes the lanes wrote.

**Not searched.**
- AlphaProof's Nature paper.
- Isabelle-specific agent work since Baldur, such as Thor's successors.
- Agda's and Idris's agent tooling.
- Lean Zulip discussions of agent cheating.

This register makes no claim about them.

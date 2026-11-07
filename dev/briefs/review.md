# Shared rules for code-review lanes

A lane brief for a review says "follow dev/briefs/review.md" and adds the scope, the time estimate and the D number range.

Rules (a paper lane, D3343: no machine load):
- Read code only. Do not edit any code, do not build, do not run tests or programs (other lanes are using the machine). The only file you add is your review document; commit just that.
- Don't merge or push, don't use git stash, don't edit board/tickets.json. Never pkill/killall. Never rm a path built from a variable.
- Run `date` at the start; at 1.5x the estimate stop and report.
- Read first: CLAUDE.md (comment style, house rules), docs/research/rust-codebase-review.md (the whole-codebase review of 1 Nov 2026: say for each of its findings in your scope whether it's still open, fixed, or changed), docs/research/architecture-review.md where relevant, and the design notes for your area in docs/proposals/. Use `git log --since=2026-10-20 -- <paths>` to see what moved recently and give recent code extra attention.
- Review for, in this order: (1) correctness and soundness risks (wrong answers, panics reachable from user input, unsafe code whose invariants aren't enforced, state that survives where it shouldn't, nondeterminism such as address-keyed tables or hash-order dependence); (2) robustness (unbounded recursion or memory, missing limits, error paths that swallow errors - D2543: limits fail, never choose); (3) design and maintainability (invariants that live only in comments, functions or files too large to reason about, duplicated logic, leaky module boundaries, dead code); (4) performance hot spots visible from the code; (5) test gaps (important behaviour with no test, tests that can't fail); (6) comments and docs against CLAUDE.md's comment rules.
- Every finding: file:line, what's wrong, a concrete scenario or why it matters, severity (high / medium / low), confidence (high / medium / low), and a recommended change with a rough size (S under 30 min, M a lane, L a design note first). Don't pad: skip nits unless they're patterns. Say what you checked and found sound, so the next reviewer needn't repeat it.
- Write docs/reviews/code-review-<NAME>.md: a summary (overall assessment in a paragraph, the top five recommendations), the findings table sorted by severity, the details, 'checked and sound', the 1 Nov review's findings' status, and 'tickets to file' as a list grouped into lanes of 30-90 min with a suggested model (DeepSeek for mechanical, Sonnet routine, Opus for kernel/unifier/unsafe/design). Questions for Matt, if any, numbered from the range given in your brief, each with a recommendation.
- Report in a few lines: the overall verdict, the top five, and how many findings by severity.

- D questions: raise few, only ones that are genuinely Matt's (direction, user-visible language, trust, process). Decide reversible and implementation choices yourself and list them as "calls I made".

- Never run the board tool (`board/board`) or edit any `board/tickets.json`, in your worktree or the main checkout: the orchestrator records your report.

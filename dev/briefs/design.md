# Shared rules for design-note lanes

You write one design note. You read code; you do not change it.

- Paper lane (D3343): no machine load. No builds, no test runs, no `stitchwort` runs, no `cargo`. Reading files,
  grep and git log/blame are fine.
- Write exactly one file, in `docs/proposals/` (the name your brief gives), and commit only
  that file on your branch. Don't edit `board/tickets.json`, don't merge, don't push, no
  `git stash`. Never `pkill`/`killall`; never `rm` a path built from a variable.
- Run `date` at the start and at each milestone. Expected time is in your brief; at 1.5x stop
  and report what's done and left; at 3x stop regardless.
- Read the reviews and notes your brief names first, and don't repeat their findings: build on them.
- Ground every claim in the code: file:line. Say how confident you are where you inferred
  rather than read.
- Write for Matt, plainly: for each part, (1) the problem, in everyday words with a concrete
  example a user would hit; (2) the change; (3) what it should do, and how we'd know. Jargon
  only after the plain version. Lead with the user-visible benefit.
- Compare at least two designs, and recommend one, with the reason. Say what it costs and what
  it rules out. Where another system (Lean, Rust, rust-analyzer, Koka, Agda, GHC...) solved the same
  problem, say how, briefly, if you know it; use the web only for a specific fact.
- Limits fail, never choose (D2543): a budget that runs out gives an error, not a different answer.
- Questions for Matt: number them from the D base your brief gives, each with a
  recommendation: `D2740: ... [rec: yes, because ...]`. Only direction and end-state
  questions; decide sequencing and implementation details yourself and say so.
- End with "Tickets to file": stages as lanes of 30-90 min each, with a model (Opus for the
  kernel, soundness, core language and tricky parts; Sonnet for routine and refactors; DeepSeek
  for mechanical, well-bounded work), an estimate, the targeted tests each should run, and the
  order. Point at existing tickets (SW-N) a stage replaces or absorbs.
- Report back briefly: the recommendation in two sentences, the D questions, the stages, and
  what you didn't cover.

- D questions: raise few, only ones that are genuinely Matt's (direction, user-visible language, trust, process). Decide reversible and implementation choices yourself and list them as "calls I made".

- Never run the board tool (`board/board`) or edit any `board/tickets.json`, in your worktree or the main checkout: the orchestrator records your report.

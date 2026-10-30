# Research register

A literature trawl for ideas to steal, one file per cluster (SW-894). Each
file records how it was searched, so it can be refreshed.

| Cluster | File | Screened / carded / read in full / not read | Status (30 Oct 2026) |
|---|---|---|---|
| Effects and handlers | [effects.md](effects.md) | 75 / 11 / 10 + C3 (a manual) / 0 | Audited against full texts |
| Elaboration | [elaboration.md](elaboration.md) | 64 / 20 / 20 / 0 | Redone from full texts |
| Proof automation | [proof-automation.md](proof-automation.md) | 72 / 29 / 25 / 4 | Redone from full texts |
| Kernel and type theory | [kernel.md](kernel.md) | 62 / 27 / 26 / 1 | Redone from full texts |
| Inductive types and recursion | [inductives.md](inductives.md) | 56 / 21 / 21 / 0 | Audited against full texts (11 OK, 8 minor, 0 wrong); C20 and C21 read in the audit; D1912 withdrawn (wrong day 21 assumption) |
| Infrastructure and trust | [infrastructure.md](infrastructure.md) | 68 / 29 / 29 / 0 | Audited against full texts (18 OK, 5 minor, 1 wrong: C1's numbers were the submission copy's); searching finished (12 more queries); C23 read in the audit; C31–C33 added; D2030; C3 (Eris) read in full from the PDF Matt fetched: T2's overwrite half becomes error enumeration, kernel first (D2031) |
| Compilation and runtime | [compilation.md](compilation.md) | 52 / 23 / 22 / 1 | Audited against full texts |
| Agentic theorem proving (SW-909) | [agentic-proving.md](agentic-proving.md) | 69 / 24 / 12 in full + 12 in part / 0 | New 30 Oct; not yet audited; with a friction count from the AoC and rogue notes; D2040–D2041 |
| Congruence closure in `cases` (SW-904, D2000) | [congruence-closure-evidence.md](congruence-closure-evidence.md) | evidence survey of the repo, not literature | New 30 Oct; recommends defer: about 150 sites, about 0 lines saved each |

**Summary report:** [summary/literature-review.pdf](summary/literature-review.pdf)
(LaTeX source and bibliography beside it; build with
`nix shell nixpkgs#texliveFull -c latexmk -pdf literature-review.tex` in that folder). It
summarises the seven registers, lists what was already acted on, gives one prioritised list
of recommendations and the open decisions, and cites only sources read in full.

A card marked NOT READ supports no ranking or recommendation. On 29 Oct
several of these files were written from abstracts; the lessons are in
board ticket SW-897.

## What a cluster file holds

1. **Method**: the queries and sources used, with the date. What couldn't be
   reached is listed too.
2. **Screened list**: one line per paper or source: keep, maybe or drop.
3. **Cards**: about five lines per kept paper: citation and link; the claim;
   what Stitchwort could steal; which ticket, note or area it helps; cost
   (small change, kernel change, research project); whether the full text
   was read.
4. **Deep reads**: the top three to five, each mapped onto Stitchwort with
   file references, risks and a next step (a ticket or a design note, never
   code).
5. **Steal next**: ranked by value against effort, then proposed tickets
   (label `research`) and at most a few decisions for Matt.

Claims are labelled as in the rest of `docs/`: **[cited]** (with a link),
**[checked]** (read in the source or our code), **[inferred]**,
**[unverified]**.

## Refreshing

Quarterly, rerun each file's queries limited to the months since its date,
screen the new hits, and add cards. Leave old entries in place and mark any
that are now done or superseded.

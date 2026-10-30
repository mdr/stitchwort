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
| Infrastructure and trust | [infrastructure.md](infrastructure.md) | 59 / 26 / 24 / 2 | Read in full (29 Oct); searching was cut short, see its §9 |
| Compilation and runtime | [compilation.md](compilation.md) | 52 / 23 / 22 / 1 | Audited against full texts |

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

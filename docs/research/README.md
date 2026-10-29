# Research register

A literature trawl for ideas to steal, one file per cluster (SW-894). Each
file records how it was searched, so it can be refreshed.

| Cluster | File |
|---|---|
| Effects and handlers | [effects.md](effects.md) |
| Elaboration | [elaboration.md](elaboration.md) |
| Proof automation | [proof-automation.md](proof-automation.md) |
| Kernel and type theory | [kernel.md](kernel.md) |
| Infrastructure and trust | [infrastructure.md](infrastructure.md) |

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

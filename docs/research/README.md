# Research register

A literature trawl for ideas to steal (SW-894). One file per cluster:

- [elaboration.md](elaboration.md): unification, postponement, implicit and instance
  arguments, records, folded goals, error messages, holes.

Each file has: the method and the exact queries (so the trawl can be rerun), a screened list
(one line per source: keep, maybe or drop), a card for each kept source, a few deep reads, a
ranked "steal next" list, proposed tickets (label `research`) and at most three decisions.

**Card format** (about five lines): citation and link; the claim; what Stitchwort could steal;
which ticket, note or area it helps; cost (small change / elaborator change / kernel change /
research project); whether the full text was reachable.

**Labels** as in docs/proposals: [cited] read in the linked source; [checked] read in our code
or docs at the place given; [inferred] reasoning; [unverified] not read, from an abstract or a
summary.

**Refreshing.** Once a quarter, rerun each file's queries, restricted to the months since the
last run; screen only what's new; add cards; note the date at the top of the file.

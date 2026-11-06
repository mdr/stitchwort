# Reviews

Reviews and longer lane reports that are worth keeping, one file each, named
`SW-N-topic.md` where N is the ticket the work belongs to (for example
`SW-1713-epics-review.md`). Link the file from its ticket's body (write its path, and
the board turns it into a link), and commit it with the work it describes.

The board lists a review on the card of the epic its ticket belongs to, so the epic
shows its reviews without anyone editing `board/epics.json`. A review of work that
belongs to no ticket gets a ticket first. A file that doesn't fit the pattern (this
README, an HTML companion) is not listed.

What goes here: a review of a design or a change, an investigation with its evidence, a
lane's report where the ticket body would be too small. What doesn't: decisions (they
go on the ticket as `D` numbers), proposals (`docs/proposals/`), and a status line a
ticket body already carries.

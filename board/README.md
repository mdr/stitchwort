# Board

The task list for Stitchwort: a small kanban board shared by Matt and the AI
agents (Claude Opus and Sonnet lanes in git worktrees, DeepSeek and GLM via
OpenCode in scratch clones). It replaces the old `TODO.md`.

- Data: [`tickets.json`](tickets.json), committed to git.
- Web page: `./board/serve.sh` (inside `nix develop`), then open
  <http://127.0.0.1:8020/>. Served on 127.0.0.1 only; `PORT=9000 ./board/serve.sh`
  picks another port. The page updates live when the file changes on disk
  (the CLI, another agent, `git pull`).
- Command line: `nix develop -c board/board <command>` (or `board/board` if
  `node` is on your PATH). Non-interactive, so agents can script it.

Only Node's standard library is used; there is nothing to install.

## Command line

```
board list [--archived] [--status S] [--agent A] [--label L] [--json]
board show N [--json]               # also finds archived tickets (read-only)
board add "title" [--status S] [--agent A] [--where W] [--label L]... [--body TEXT | --body-file F]
board move N STATUS
board assign N AGENT [--where W]     # a backlog/next ticket also moves to doing
board unassign N                     # clears agent and where
board edit N [--title T] [--status S] [--agent A] [--where W] [--body TEXT | --body-file F]
             [--label L]...          # replace the labels
             [--add-label L]... [--rm-label L]...
board commit N HASH...               # record commits on the ticket
board rm N
board archive --before DATE         # move old done tickets to board/archive/
```

- `N` is a ticket number, written `12` or `SW-12`.
- `add` prints the new id (`SW-12`), so scripts can capture it:
  `id=$(board/board add "Fix the thing" --label bug)`.
- `--body-file -` reads the body from standard input.
- `archive` is described under "Archive" below.
- Statuses: `backlog`, `next`, `doing`, `review`, `done`.
- Agents: `Opus`, `Sonnet`, `DeepSeek`, `GLM`, `Matt`, `Claude`, or empty.
- Errors go to standard error with a message and exit status 1 (2 for no command).
- `BOARD_FILE=/path/to/file.json` points the CLI and the server at another file
  (the tests use this).

## Data format

`tickets.json` is pretty-printed with a stable key order, tickets sorted by
number, so diffs are readable.

```json
{
  "next": 13,
  "tickets": [
    {
      "id": 12,
      "title": "One line",
      "status": "backlog | next | doing | review | done",
      "agent": "",
      "where": "worktree, branch or clone path, or empty",
      "labels": ["elab", "bug"],
      "body": "markdown, as long as it needs to be",
      "created": "2026-10-19",
      "updated": "2026-10-19",
      "commits": ["abc1234"]
    }
  ]
}
```

- Tickets display as `SW-12`. Numbers are unique and never reused: `next` is the
  number the next ticket gets, it only increases, and `rm` does not give a
  number back. (If the file is edited by hand so `next` is too low, loading
  raises it above the largest id.)
- Within a column the web page lists tickets by number (lowest first), except
  Done, which shows the most recently updated first. Number order is therefore
  priority order inside Backlog and Next: add tickets to Next in the order the
  work should happen, or move them with `edit`/`move` as plans change.
- Writes are atomic (a temporary file in the same directory, then a rename) and
  every change re-reads the file first, under a lock directory
  (`tickets.json.lock`), so the CLI and the server never overwrite each other's
  changes. If a crashed process leaves the lock behind, it is ignored after 10
  seconds.
- Labels are free text. The ones in use: `kernel`, `elab`, `syntax`, `js`,
  `web`, `playground`, `aoc`, `docs`, `design`, `multi-file`, `tooling`,
  `stdlib`, `proof`, `bug`.

## Archive

To keep the board small, finished work moves out of `tickets.json` into
`board/archive/YYYY-MM.json` (the month of the ticket's `updated` date, which for
a done ticket is when it was finished). The files have the same ticket format,
wrapped as `{ "tickets": [...] }`, sorted by number, with no `next`.

```
board archive --before 2026-10-23   # every done ticket with updated < 2026-10-23
```

Rule: only `done` tickets are archived, and only those whose `updated` date is
strictly before DATE; the command is repeatable and merges into existing archive
files. Run it now and then with a date a day or two back, so recent done work
stays visible on the board. The first run (24 Oct 2026, `--before 2026-10-23`)
moved 297 tickets.

- Numbers are never reused: `next` in `tickets.json` is untouched by archiving, so
  `add` continues from it.
- `board show N` falls back to the archive and marks the ticket "(archived,
  read-only)"; `board list --archived` lists archived tickets (with the usual
  filters). `move`, `edit`, `assign`, `commit` and `rm` on an archived ticket
  fail with "SW-N is archived (read-only)". To change one, edit the archive file
  by hand.
- The web page and its API show only live tickets.
- The archive files are written before the board file, so a crash can leave a
  ticket in both (running the command again fixes it), never in neither.

## Web page

Columns Backlog, Next, In progress, Review, Done (Done shows the most recent
twelve; "Show all" expands it). Cards show the id, title, agent (coloured chip),
labels and `where`. Drag a card to another column to move it, click it to edit
every field (the body is plain text with a simple markdown preview), use
"+ Add ticket" (or a column's +) to create one. Delete asks for confirmation in
the page. Filter by agent, label or text; the bar under the header shows who has
what in progress or review.

The JSON API used by the page: `GET /api/board`, `POST /api/tickets`,
`PATCH /api/tickets/N`, `DELETE /api/tickets/N`, and `GET /api/events`
(Server-Sent Events, one `changed` event per file change).

## Conventions for agents

1. Take a ticket: `board assign N <your name> --where <worktree, branch or clone>`
   (this also moves it to `doing`). Work only on tickets assigned to you, or
   tickets you created for the work.
2. When you finish and the work is ready to be reviewed, move it:
   `board move N review`. Put anything the reviewer needs to know in the body
   (`board edit N --body-file notes.md`), or write the details in your final
   report.
3. The orchestrator reviews and merges, then records the commits and moves the
   ticket to done: `board commit N <hash>` and `board move N done`.
4. Findings you do not act on become new backlog tickets
   (`board add "title" --label bug --body "..."`), not edits to unrelated
   tickets. Do not put a new finding straight into `next` unless it blocks work in
   progress.
5. Keep ticket bodies as the place for the full detail (decisions, links,
   commit hashes, dates). One ticket per piece of work.
6. Worktrees and clones each have their own copy of `tickets.json`. The board
   Matt sees is the one on `main`'s checkout, so agents that should show up
   live point the CLI at that file: `export BOARD_FILE=<main checkout>/board/tickets.json`
   (the orchestrator says which path). Only the orchestrator commits
   `tickets.json`, together with the merge it describes; agents do not commit it
   from their lane branches (that would conflict). Agents in scratch clones
   without access to that path report their ticket changes in their final report
   and the orchestrator applies them.

Process notes (lanes, model tiers, the commit gate) are in
[../docs/workflow.md](../docs/workflow.md); what was done before the board is in
[../docs/history.md](../docs/history.md).

## Tests

```
nix develop -c node --test board/board.test.js
```

They run in `nix flake check` too (the `board` check).

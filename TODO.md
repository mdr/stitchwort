# To do

The task list is the kanban board, not this file.

- Run it: `nix develop -c ./board/serve.sh`, then open <http://127.0.0.1:8020/>.
- Data: [`board/tickets.json`](board/tickets.json) (committed).
- Command line: `board/board list`, `show N`, `add "title"`, `move N STATUS`,
  `assign N AGENT`, `edit N`, `commit N HASH`, `rm N`. See
  [board/README.md](board/README.md) for the full reference and the
  conventions agents follow.
- What was done before the board, and the old status notes:
  [docs/history.md](docs/history.md). How work is organised:
  [docs/workflow.md](docs/workflow.md).

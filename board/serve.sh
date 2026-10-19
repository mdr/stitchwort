#!/usr/bin/env bash
# Serves the kanban board on this machine only:
#   ./board/serve.sh            port 8020
#   PORT=9000 ./board/serve.sh
# Run inside `nix develop`, which provides Node.
set -euo pipefail
cd "$(dirname "$0")"
exec node server.js

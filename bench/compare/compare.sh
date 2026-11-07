#!/usr/bin/env bash
# `task bench:compare`: Stitchwort against CPython, PyPy and Lean
# (docs/proposals/comparative-speed.md). Run inside `nix develop .#compare`.
#
#   bash bench/compare/compare.sh --sw path/to/stitchwort [--check] [--runs N]
#                                 [--all] [NAME...]
#
# See bench/compare/README.md. The work is in compare.py.
set -euo pipefail
exec python3 -I "$(dirname "$0")/compare.py" "$@"

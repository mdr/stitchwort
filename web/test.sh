#!/usr/bin/env bash
# Builds the WebAssembly bundle, then runs the playground's browser tests in
# headless Chrome (web/tests/browser.mjs; see docs/testing.md):
#   ./web/test.sh               build, then test
#   ./web/test.sh --no-build    test what's already built
#   ./web/test.sh Run Stop      only the tests whose names contain these
# Run inside `nix develop`, which provides the build tools and Node. Chrome
# comes from the system; without it, the tests are skipped.
set -euo pipefail
cd "$(dirname "$0")/.."
if [ "${1:-}" = "--no-build" ]; then
  shift
else
  ./web/build.sh > /dev/null
fi
exec node web/tests/browser.mjs "$@"

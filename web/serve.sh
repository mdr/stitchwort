#!/usr/bin/env bash
# Builds the WebAssembly bundle and serves web/ on this machine only:
#   ./web/serve.sh             build, then serve on port 8000
#   ./web/serve.sh --no-build  serve what's already built
#   PORT=9000 ./web/serve.sh
# Run inside `nix develop`, which provides the build tools.
set -euo pipefail
cd "$(dirname "$0")"
if [ "${1:-}" != "--no-build" ]; then
  ./build.sh
fi
PORT="${PORT:-8000}"
echo "Playground:   http://127.0.0.1:$PORT/index.html"
echo "Stress tests: http://127.0.0.1:$PORT/stress.html"
# A plain static server, but with the right type for .wasm (some Pythons
# don't know it), so the browser can compile the module as it downloads.
exec python3 -c '
import http.server, sys
handler = http.server.SimpleHTTPRequestHandler
handler.extensions_map[".wasm"] = "application/wasm"
handler.extensions_map[".js"] = "text/javascript"
http.server.ThreadingHTTPServer(("127.0.0.1", int(sys.argv[1])), handler).serve_forever()
' "$PORT"

#!/usr/bin/env bash
# Writes SITE_DIR/pkg/version.json for content-hash caching (docs/proposals/
# playground-projects.md §10.2):
#   web/write-version.sh SITE_DIR
# SITE_DIR holds playground-worker.js and pkg/ (web/ locally, the Nix output
# in the `playground` package). The file is {"compiler": H, "projects": H}:
# a short hash of the compiler's files (the WebAssembly, the bindings and the
# worker script) and one of the bundled projects. The page fetches it with
# `cache: "no-cache"` and asks for the other files as `?v=H`.
set -euo pipefail
export LC_ALL=C
cd "$1"

# sha256 of stdin, as 64 hex digits (GNU and macOS).
digest() {
  if command -v sha256sum >/dev/null; then sha256sum | cut -d' ' -f1; else shasum -a 256 | cut -d' ' -f1; fi
}

compiler=$(cat pkg/stitchwort_web_bg.wasm pkg/stitchwort_web.js playground-worker.js | digest | cut -c1-16)
# One line per file (its own hash and path, sorted), so a renamed file changes it.
projects=$(
  cd pkg/projects
  for f in $(find . -type f | sort); do
    printf '%s %s\n' "$(digest <"$f")" "$f"
  done | digest | cut -c1-16
)
printf '{"compiler": "%s", "projects": "%s"}\n' "$compiler" "$projects" >pkg/version.json
echo "version: compiler $compiler, projects $projects"

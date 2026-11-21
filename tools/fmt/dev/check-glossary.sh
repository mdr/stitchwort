#!/usr/bin/env bash
# Checks tools/fmt/GLOSSARY.md and PROOF-MAP.md against the sources: every `name` (path.sw:N) reference must
# name an existing file whose line N holds the name (its last dotted part), and every path in a PROOF-MAP link
# must exist. Run from anywhere: dev/check-glossary.sh. Prints each bad reference; exit 1 if any.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 -I - "$@" <<'PY'
import re, sys, pathlib
root = pathlib.Path('.')
roots = [root / 'src', root / '../..']
def find(path):
    for r in roots:
        for cand in (r / path,):
            if cand.is_file():
                return cand
    return None
bad = 0
ref = re.compile(r'`([^`]+)`\s*\(([\w/.-]+\.sw):(\d+)((?:,\s*\d+)*)\)')
for doc in ('GLOSSARY.md', 'PROOF-MAP.md'):
    if not pathlib.Path(doc).is_file():
        continue
    text = pathlib.Path(doc).read_text()
    for m in ref.finditer(text):
        name, path, line = m.group(1), m.group(2), int(m.group(3))
        f = find(path)
        if f is None:
            print(f'{doc}: no file {path}'); bad += 1; continue
        lines = f.read_text().split('\n')
        if line > len(lines) or name.split('.')[-1].split()[0] not in lines[line - 1]:
            print(f'{doc}: `{name}` not on {path}:{line}'); bad += 1
    for m in re.finditer(r'\]\((src/[\w/.-]+\.sw)\)', text):
        if not (root / m.group(1)).is_file():
            print(f'{doc}: broken link {m.group(1)}'); bad += 1
mp = pathlib.Path('PROOF-MAP.md')
if mp.is_file():
    seen = {}
    for row in mp.read_text().split('\n'):
        m = re.match(r'\| \*\*(G-[\w-]+)\*\*', row)
        if not m:
            continue
        for pat in re.findall(r'`([\w/*]+\.sw)`', row):
            hits = sorted((root / 'src').glob(pat))
            if not hits:
                print(f'PROOF-MAP.md: {m.group(1)}: {pat} matches no file'); bad += 1
            for h in hits:
                if h in seen and seen[h] != m.group(1):
                    print(f'PROOF-MAP.md: {h} in {seen[h]} and {m.group(1)}'); bad += 1
                seen[h] = m.group(1)
    for f in sorted((root / 'src').rglob('*.sw')):
        if 'Tests' not in f.parts and f not in seen:
            print(f'PROOF-MAP.md: {f.relative_to(root / "src")} is in no group'); bad += 1
print('ok' if bad == 0 else f'{bad} bad references')
sys.exit(1 if bad else 0)
PY

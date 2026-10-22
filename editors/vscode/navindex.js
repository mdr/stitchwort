'use strict';
// Pure lookup logic over a Stitchwort navigation index (version 2, see
// docs/proposals/code-navigation.md). No `vscode` import, so it runs under
// plain `node --test`. Ranges are [startLine, startChar, endLine, endChar],
// 0-based, UTF-16, end exclusive.

function cmp(line, ch, l, c) {
  return line !== l ? line - l : ch - c;
}

function contains(range, line, ch) {
  return (
    cmp(line, ch, range[0], range[1]) >= 0 && cmp(line, ch, range[2], range[3]) < 0
  );
}

function fileIndexByPath(index, path) {
  return index.files.findIndex((f) => f.path === path);
}

// The index entry of an embedded library file, by its `std` value
// (`List/Toolkit.sw`; `core/Data.sw` is a file of the core), or -1.
function fileIndexByStd(index, std) {
  return index.files.findIndex((f) => f.std === std);
}

// The `std` value of a `stitchwort-std:` document, from its URI path.
function stdOfPath(uriPath) {
  return uriPath.replace(/^\//, '');
}

// Which index to answer from for a library document: among `candidates`
// ({key, index, ...}), the one under `preferKey` (the project the document was
// opened from) if it has refs in that library file, else the first that has.
// Returns {candidate, file} or null. A library file's refs exist only in the
// indexes of programs that loaded it.
function pickIndexForStd(candidates, std, preferKey) {
  const has = (c) => {
    const file = fileIndexByStd(c.index, std);
    return file >= 0 && c.index.refs.some((r) => r.file === file) ? file : -1;
  };
  const ordered = [
    ...candidates.filter((c) => c.key === preferKey),
    ...candidates.filter((c) => c.key !== preferKey),
  ];
  for (const candidate of ordered) {
    const file = has(candidate);
    if (file >= 0) return { candidate, file };
  }
  return null;
}

// The ref whose range contains the position, within one file (an index into
// `index.files`). Refs are sorted by file then position, so binary search for
// the first ref ending after the position.
function refAt(index, file, line, ch) {
  const refs = index.refs;
  let lo = 0;
  let hi = refs.length;
  while (lo < hi) {
    const mid = (lo + hi) >> 1;
    const r = refs[mid];
    const before =
      r.file < file ||
      (r.file === file && cmp(r.range[2], r.range[3], line, ch) <= 0);
    if (before) lo = mid + 1;
    else hi = mid;
  }
  const r = refs[lo];
  return r && r.file === file && contains(r.range, line, ch) ? r : null;
}

// Where a ref points: {file (index), path, std, range} or null.
function targetOf(index, ref) {
  if (!ref) return null;
  let file;
  let range;
  if (ref.binder) {
    file = ref.binder.file;
    range = ref.binder.range;
  } else if (ref.symbol !== undefined && ref.symbol !== null) {
    const s = index.symbols[ref.symbol];
    if (!s) return null;
    file = s.file;
    range = s.range;
  } else {
    return null;
  }
  const f = index.files[file];
  if (!f) return null;
  return { file, path: f.path, std: f.std || null, range };
}

// Hover facts: {type, name, kind}; name/kind only for declarations and locals.
function hoverOf(index, ref) {
  if (!ref) return null;
  const out = { type: ref.type || null, name: null, kind: null };
  if (ref.symbol !== undefined && ref.symbol !== null) {
    const s = index.symbols[ref.symbol];
    if (s) {
      out.name = s.name;
      out.kind = s.kind;
      if (!out.type) out.type = s.type || null;
    }
  } else if (ref.binder) {
    out.name = ref.binder.name;
    out.kind = 'local';
  }
  return out;
}

// The outline of one file: symbols with a fullRange, nested by container.
// Returns [{name, qualified, kind, type, range, fullRange, children}] where
// name is the short name (after the last dot of the qualified one).
function outlineOf(index, file) {
  const nodes = new Map();
  index.symbols.forEach((s, i) => {
    if (s.file !== file || !s.fullRange) return;
    const short = s.name.slice(s.name.lastIndexOf('.') + 1) || s.name;
    nodes.set(i, {
      name: short,
      qualified: s.name,
      kind: s.kind,
      type: s.type || null,
      range: s.range,
      fullRange: s.fullRange,
      children: [],
    });
  });
  const roots = [];
  for (const [i, node] of nodes) {
    const parent = nodes.get(index.symbols[i].container);
    (parent ? parent.children : roots).push(node);
  }
  return roots;
}


function sameRange(a, b) {
  return a[0] === b[0] && a[1] === b[1] && a[2] === b[2] && a[3] === b[3];
}

function sameSpot(a, b) {
  return a.file === b.file && sameRange(a.range, b.range);
}

// The locations of everything that refers to the same declaration or local
// variable as `ref` (all refs with the same `symbol`, or the same `binder`),
// as targets ({file, path, std, range}), in index order. The declaration's
// own name is among them if `includeDeclaration`, and not otherwise (the
// index has a ref there too, for a declaration; a local's binder has none).
function referencesTo(index, ref, includeDeclaration) {
  const decl = targetOf(index, ref);
  if (!decl) return [];
  const isSymbol = ref.symbol !== undefined && ref.symbol !== null;
  const out = [];
  for (const r of index.refs) {
    const same = isSymbol
      ? r.symbol === ref.symbol
      : r.binder && r.binder.file === ref.binder.file && sameRange(r.binder.range, ref.binder.range);
    if (!same) continue;
    const f = index.files[r.file];
    if (!f) continue;
    const here = { file: r.file, path: f.path, std: f.std || null, range: r.range };
    if (sameSpot(here, decl)) continue;
    out.push(here);
  }
  if (includeDeclaration) out.push(decl);
  out.sort((a, b) => a.file - b.file || cmp(a.range[0], a.range[1], b.range[0], b.range[1]));
  return out;
}

// The index's diagnostics as editor diagnostics, by project file path (library
// files are skipped; a diagnostic with no location has no file to show on).
// Each is {path, severity ('error'|'warning'), code, range, message, related:
// [{path, std, range, message}]}. The message is the main text, then the first
// label's explanation and the notes, one per line.
function diagnosticsByFile(index) {
  const out = new Map();
  for (const d of index.diagnostics || []) {
    if (d.file === undefined || d.file === null) continue;
    const f = index.files[d.file];
    if (!f || f.std) continue;
    const lines = [d.message];
    const labels = d.labels || [];
    if (labels[0] && labels[0].message && labels[0].message !== d.message) {
      lines.push(labels[0].message);
    }
    for (const n of d.notes || []) lines.push(`Note: ${n}`);
    const related = [];
    for (const l of labels.slice(1)) {
      const lf = index.files[l.file];
      if (lf) related.push({ path: lf.path, std: lf.std || null, range: l.range, message: l.message });
    }
    if (!out.has(f.path)) out.set(f.path, []);
    out.get(f.path).push({
      path: f.path,
      severity: d.severity === 'warning' ? 'warning' : 'error',
      code: d.code,
      range: d.range,
      message: lines.join('\n'),
      related,
    });
  }
  return out;
}

// The namespace a file's `namespace` line names (`namespace Aoc.Day01`), or
// null. As in the parser, it is the file's first declaration (only blank lines
// and `--` comments come before it), at the start of a line.
function namespaceOf(text) {
  for (const line of text.split(/\r?\n/)) {
    if (/^\s*$/.test(line) || line.startsWith('--')) continue;
    const m = /^namespace[ \t]+([A-Z][A-Za-z0-9_']*(?:\.[A-Z][A-Za-z0-9_']*)*)(?![\w'.])/.exec(line);
    return m ? m[1] : null;
  }
  return null;
}

// Diagnostics after a quick run of some namespaces. `current` is the shown
// diagnostics (path -> list, as from diagnosticsByFile) and `quick` the index
// of the quick run. The quick run is newer than whatever `current` holds
// for the files it checked (each of its non-library files), so those files get
// its diagnostics, or none; every other file keeps what it had until the next
// full run replaces everything. Returns a new Map.
function applyQuick(current, quick) {
  const out = new Map(current);
  const fresh = diagnosticsByFile(quick);
  for (const f of quick.files || []) {
    if (f.std) continue;
    if (fresh.has(f.path)) out.set(f.path, fresh.get(f.path));
    else out.delete(f.path);
  }
  return out;
}

// Whether the letters of `query` appear in order in `name`, ignoring case.
function subsequence(query, name) {
  const n = name.toLowerCase();
  let at = 0;
  for (const ch of query.toLowerCase()) {
    at = n.indexOf(ch, at);
    if (at < 0) return false;
    at++;
  }
  return true;
}

// Workspace symbols: the definitions of the checked files (those with a
// fullRange) whose qualified name matches `query`, best first (exact short
// name, then substring, then letters in order). Each is {name (short),
// qualified, kind, container (qualified name or null), path, range}.
function workspaceSymbols(index, query) {
  const q = (query || '').toLowerCase();
  const scored = [];
  index.symbols.forEach((s, i) => {
    if (!s.fullRange) return;
    const f = index.files[s.file];
    if (!f || f.std) return;
    const short = s.name.slice(s.name.lastIndexOf('.') + 1) || s.name;
    let score;
    if (!q) score = 3;
    else if (short.toLowerCase() === q) score = 0;
    else if (s.name.toLowerCase().includes(q)) score = 1;
    else if (subsequence(q, s.name)) score = 2;
    else return;
    const parent =
      s.container !== undefined && s.container !== null ? index.symbols[s.container] : null;
    scored.push({
      score,
      i,
      sym: {
        name: short,
        qualified: s.name,
        kind: s.kind,
        container: parent ? parent.name : null,
        path: f.path,
        range: s.range,
      },
    });
  });
  scored.sort((a, b) => a.score - b.score || a.i - b.i);
  return scored.map((x) => x.sym);
}

module.exports = {
  applyQuick,
  contains,
  diagnosticsByFile,
  fileIndexByPath,
  fileIndexByStd,
  hoverOf,
  namespaceOf,
  outlineOf,
  pickIndexForStd,
  refAt,
  referencesTo,
  stdOfPath,
  targetOf,
  workspaceSymbols,
};

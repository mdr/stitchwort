'use strict';
// Pure lookup logic over a Stitchwort navigation index (version 1, see
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

// A ref-like record for the declaration whose own name is at the position
// (declaration sites have no ref of their own), so hover works there too.
function declAt(index, file, line, ch) {
  for (let i = 0; i < index.symbols.length; i++) {
    const s = index.symbols[i];
    if (s.file === file && s.fullRange && contains(s.range, line, ch)) {
      return { file, range: s.range, symbol: i, type: s.type };
    }
  }
  return null;
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

module.exports = { contains, declAt, fileIndexByPath, refAt, targetOf, hoverOf, outlineOf };

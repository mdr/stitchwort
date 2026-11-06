'use strict';
// Shared by the server (Node) and the pages (browser, as BoardLinks): the patterns
// that turn repo paths, ticket numbers and decision numbers in text into links.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.BoardLinks = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  // Extensions /doc will serve: markdown as a page, the rest as numbered plain text.
  const MARKDOWN_EXTS = ['md'];
  const TEXT_EXTS = ['sw', 'txt', 'rs', 'toml', 'json', 'js', 'mjs', 'ts', 'html', 'css', 'nix', 'sh', 'yml', 'yaml'];
  const EXT_RE = [...MARKDOWN_EXTS, ...TEXT_EXTS].join('|');

  // One alternation: a repo path (with at least one directory, optional :line),
  // a ticket (SW-1642) or a decision (D2514).
  const PATTERN = String.raw`(?<path>(?<![\w/.\-])(?:[A-Za-z0-9_.\-]+/)+[A-Za-z0-9_.\-]+\.(?:${EXT_RE})\b)(?::(?<line>\d+))?|\b(?<ticket>SW-\d+)\b|\b(?<decision>D\d{3,5})\b`;

  // Splits text into [{ text }] and [{ text, kind: 'path'|'ticket'|'decision', ... }].
  function tokenize(text) {
    const re = new RegExp(PATTERN, 'g');
    const out = [];
    let last = 0, m;
    while ((m = re.exec(text))) {
      if (m.index > last) out.push({ text: text.slice(last, m.index) });
      const g = m.groups;
      if (g.path) out.push({ text: m[0], kind: 'path', path: g.path, line: g.line ? Number(g.line) : null });
      else if (g.ticket) out.push({ text: m[0], kind: 'ticket', id: Number(g.ticket.slice(3)) });
      else out.push({ text: m[0], kind: 'decision', decision: g.decision });
      last = m.index + m[0].length;
    }
    if (last < text.length) out.push({ text: text.slice(last) });
    return out;
  }

  const extOf = (p) => {
    const m = /\.([A-Za-z0-9]+)$/.exec(p);
    return m ? m[1].toLowerCase() : '';
  };
  // 'markdown', 'text' or null (not something /doc serves).
  function docKind(p) {
    const e = extOf(p);
    if (MARKDOWN_EXTS.includes(e)) return 'markdown';
    if (TEXT_EXTS.includes(e)) return 'text';
    return null;
  }

  function docHref(p, line) {
    return '/doc/' + p.split('/').map(encodeURIComponent).join('/') + (line ? '#L' + line : '');
  }

  // Resolves a link written inside the document `from` (repo-relative) against it.
  // Returns { path, fragment } or null for external, empty or root-escaping links.
  function resolveRelative(from, href) {
    if (!href || /^[a-z][a-z0-9+.\-]*:/i.test(href) || href.startsWith('//')) return null;
    const hash = href.indexOf('#');
    const fragment = hash < 0 ? '' : href.slice(hash + 1);
    let target = hash < 0 ? href : href.slice(0, hash);
    try { target = decodeURIComponent(target); } catch (_) { return null; }
    if (!target) return { path: from, fragment };
    const parts = target.startsWith('/') ? [] : from.split('/').slice(0, -1);
    for (const seg of target.split('/')) {
      if (seg === '' || seg === '.') continue;
      if (seg === '..') { if (!parts.length) return null; parts.pop(); } else parts.push(seg);
    }
    return { path: parts.join('/'), fragment };
  }

  return { tokenize, docKind, docHref, resolveRelative, EXT_RE, MARKDOWN_EXTS, TEXT_EXTS };
});

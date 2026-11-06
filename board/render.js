'use strict';
// Browser-side markdown for the board and the document pages (BoardRender). Built
// from DOM nodes only, never innerHTML, so text from a file cannot inject markup.
// Needs links.js (BoardLinks) loaded first.
(function () {
  const L = BoardLinks;

  function el(tag, props, ...kids) {
    const e = document.createElement(tag);
    for (const [k, v] of Object.entries(props || {})) {
      if (k === 'text') e.textContent = v;
      else if (k.startsWith('on')) e.addEventListener(k.slice(2), v);
      else e.setAttribute(k, v);
    }
    for (const kid of kids.flat()) if (kid != null) e.append(kid);
    return e;
  }

  // ctx: { doc: repo path of the document being shown (or null),
  //        onTicket(id), onFind(text): optional in-page handlers for SW-N and D-numbers,
  //        headingBase: added to heading levels (tickets use 2 so # is an h3) }

  // Plain text with repo paths, tickets and decisions turned into links.
  function linkify(text, parent, ctx = {}) {
    for (const seg of L.tokenize(text)) {
      if (!seg.kind || ctx.nolink) { parent.append(seg.text); continue; }
      if (seg.kind === 'path') {
        parent.append(el('a', { href: L.docHref(seg.path, seg.line), target: ctx.doc ? '_self' : '_blank', rel: 'noopener', text: seg.text }));
      } else if (seg.kind === 'ticket') {
        parent.append(el('a', { href: '/#ticket/' + seg.id, text: seg.text,
          onclick: ctx.onTicket ? (ev) => { ev.preventDefault(); ev.stopPropagation(); ctx.onTicket(seg.id); } : (ev) => ev.stopPropagation() }));
      } else {
        parent.append(el('a', { href: '/#find/' + seg.decision, text: seg.text,
          onclick: ctx.onFind ? (ev) => { ev.preventDefault(); ev.stopPropagation(); ctx.onFind(seg.decision); } : (ev) => ev.stopPropagation() }));
      }
    }
    return parent;
  }

  // A link written in markdown: external, an anchor in this document, or relative.
  function linkEl(href, kids, ctx) {
    if (/^https?:\/\//i.test(href)) return el('a', { href, target: '_blank', rel: 'noopener' }, kids);
    if (href.startsWith('#')) return el('a', { href }, kids);
    const r = ctx.doc != null ? L.resolveRelative(ctx.doc, href) : null;
    if (r && L.docKind(r.path)) {
      const lineM = /^L(\d+)$/.exec(r.fragment);
      const h = L.docHref(r.path, lineM ? Number(lineM[1]) : 0) + (r.fragment && !lineM ? '#' + encodeURIComponent(r.fragment) : '');
      return el('a', { href: h }, kids);
    }
    return el('span', { class: 'deadlink', title: href }, kids);
  }

  const INLINE = new RegExp([
    String.raw`\\[\\\x60*_{}\[\]()#+\-.!|<>]`, // 0: escape
    String.raw`\x60+[^\x60]+\x60+`, // code span
    String.raw`!?\[((?:[^\[\]]|\[[^\]]*\])*)\]\(\s*<?([^)\s>]+)>?(?:\s+"[^"]*")?\s*\)`, // link, image
    String.raw`<(https?:\/\/[^>\s]+)>`, // <url>
    String.raw`https?:\/\/[^\s)<>]+[^\s)<>.,;:!?'"]`, // bare url
    String.raw`\*\*(?=\S)(?:[^*]|\*(?!\*))+?\*\*`, // bold
    String.raw`(?<![\w*])\*(?=[^\s*])[^*]+?(?<=[^\s*])\*(?![\w*])`, // *em*
    String.raw`(?<![\w])_(?=[^\s_])[^_]+?(?<=[^\s_])_(?![\w])`, // _em_
  ].join('|'), 'g');

  function inline(text, parent, ctx) {
    let last = 0, m;
    const re = new RegExp(INLINE.source, 'g');
    while ((m = re.exec(text))) {
      if (m.index > last) linkify(text.slice(last, m.index), parent, ctx);
      const s = m[0];
      if (s[0] === '\\') parent.append(s[1]);
      else if (s[0] === '`') {
        const n = /^`+/.exec(s)[0].length;
        const code = el('code');
        linkify(s.slice(n, -n).trim(), code, ctx);
        parent.append(code);
      } else if (m[2] !== undefined) {
        const kids = el('span');
        inline(m[1], kids, { ...ctx, nolink: true });
        const node = s[0] === '!' ? el('span', { class: 'deadlink', title: m[2] }, kids.childNodes.length ? [...kids.childNodes] : 'image') : linkEl(m[2], [...kids.childNodes], ctx);
        parent.append(node);
      } else if (s[0] === '<') parent.append(el('a', { href: m[3], target: '_blank', rel: 'noopener', text: m[3] }));
      else if (s.startsWith('http')) parent.append(el('a', { href: s, target: '_blank', rel: 'noopener', text: s }));
      else if (s.startsWith('**')) { const b = el('strong'); inline(s.slice(2, -2), b, ctx); parent.append(b); }
      else { const e = el('em'); inline(s.slice(1, -1), e, ctx); parent.append(e); }
      last = m.index + s.length;
    }
    if (last < text.length) linkify(text.slice(last), parent, ctx);
    return parent;
  }

  const indentOf = (l) => /^\s*/.exec(l)[0].replace(/\t/g, '    ').length;
  const MARKER = /^(\s*)([-*+]|\d+[.)])\s+(.*)$/;
  const FENCE = /^\s*(```+|~~~+)/;
  const HEADING = /^(#{1,6})\s+(.*?)\s*#*\s*$/;
  const HR = /^\s*([-*_])(\s*\1){2,}\s*$/;
  const TABLE_SEP = /^\s*\|?\s*:?-{2,}:?\s*(\|\s*:?-{2,}:?\s*)*\|?\s*$/;

  const cells = (row) => row.trim().replace(/^\|/, '').replace(/\|$/, '').split(/(?<!\\)\|/).map((c) => c.trim().replace(/\\\|/g, '|'));
  const slug = (t) => t.toLowerCase().replace(/[^\p{L}\p{N}\s_-]/gu, '').trim().replace(/\s/g, '-');

  function startsBlock(lines, i) {
    const l = lines[i];
    return FENCE.test(l) || HEADING.test(l) || HR.test(l) || /^\s*>/.test(l) ||
      /^\s*([-*+]|1[.)])\s+\S/.test(l) || (l.includes('|') && i + 1 < lines.length && TABLE_SEP.test(lines[i + 1]) && !TABLE_SEP.test(l));
  }

  // Returns an array of nodes. `top` is the 1-based number of lines[0] in the source
  // (set for top-level blocks, which get data-line so #L<n> can find them).
  function blocks(lines, ctx, top) {
    const out = [];
    const at = (node, i) => { if (top && node) node.setAttribute('data-line', String(top + i)); return node; };
    let i = 0;
    while (i < lines.length) {
      const line = lines[i];
      const start = i;
      let m;
      if (!line.trim()) { i++; continue; }
      if (line.trim().startsWith('<!--')) {
        while (i < lines.length && !lines[i].includes('-->')) i++;
        i++; continue;
      }
      if ((m = FENCE.exec(line))) {
        const fence = m[1][0].repeat(m[1].length);
        const buf = []; i++;
        while (i < lines.length && !lines[i].trim().startsWith(fence)) buf.push(lines[i++]);
        i++;
        out.push(at(el('pre', {}, el('code', { text: buf.join('\n') })), start));
      } else if ((m = HEADING.exec(line))) {
        const level = Math.min(6, m[1].length + (ctx.headingBase || 0));
        const h = el('h' + level, { id: slug(m[2].replace(/[`*_]/g, '')) });
        inline(m[2], h, ctx);
        out.push(at(h, start)); i++;
      } else if (HR.test(line)) {
        out.push(at(el('hr'), start)); i++;
      } else if (/^\s*>/.test(line)) {
        const buf = [];
        while (i < lines.length && /^\s*>/.test(lines[i])) buf.push(lines[i++].replace(/^\s*> ?/, ''));
        out.push(at(el('blockquote', {}, blocks(buf, ctx, 0)), start));
      } else if (line.includes('|') && i + 1 < lines.length && TABLE_SEP.test(lines[i + 1])) {
        const head = cells(line);
        const aligns = cells(lines[i + 1]).map((c) => (/^:-*:$/.test(c) ? 'center' : /-:$/.test(c) ? 'right' : ''));
        i += 2;
        const rows = [];
        while (i < lines.length && lines[i].trim() && lines[i].includes('|')) rows.push(cells(lines[i++]));
        const cell = (tag, c, k) => { const e = el(tag, aligns[k] ? { style: 'text-align:' + aligns[k] } : {}); inline(c || '', e, ctx); return e; };
        out.push(at(el('div', { class: 'tablewrap' }, el('table', {},
          el('thead', {}, el('tr', {}, head.map((c, k) => cell('th', c, k)))),
          el('tbody', {}, rows.map((r) => el('tr', {}, head.map((_, k) => cell('td', r[k], k))))))), start));
      } else if ((m = MARKER.exec(line))) {
        const n = indentOf(line);
        const ordered = /\d/.test(m[2][0]);
        const list = el(ordered ? 'ol' : 'ul');
        if (ordered && Number(m[2].replace(/\D/g, '')) !== 1) list.setAttribute('start', m[2].replace(/\D/g, ''));
        while (i < lines.length) {
          const im = MARKER.exec(lines[i]);
          if (!im || indentOf(lines[i]) !== n || /\d/.test(im[2][0]) !== ordered) break;
          const itemLines = [im[3]];
          const rest = [];
          i++;
          while (i < lines.length) {
            const l = lines[i];
            if (!l.trim()) {
              let k = i;
              while (k < lines.length && !lines[k].trim()) k++;
              if (k < lines.length && indentOf(lines[k]) > n) { rest.push(l); i++; continue; }
              break;
            }
            if (indentOf(l) > n) { rest.push(l); i++; continue; }
            // lazy continuation of a paragraph line
            const prev = rest.length ? rest[rest.length - 1] : itemLines[0];
            if (prev.trim() && !MARKER.test(l) && !startsBlock(lines, i) && !FENCE.test(prev)) { rest.push(l); i++; continue; }
            break;
          }
          const nonblank = rest.filter((r) => r.trim());
          const cut = nonblank.length ? Math.min(...nonblank.map(indentOf)) : 0;
          const body = [itemLines[0], ...rest.map((r) => r.replace(new RegExp(`^ {0,${cut}}`), ''))];
          const kids = blocks(body, ctx, 0);
          const li = el('li');
          if (kids.length === 1 && kids[0].tagName === 'P') li.append(...kids[0].childNodes);
          else if (kids.length > 1 && kids[0].tagName === 'P' && !body.slice(1).some((r) => !r.trim())) { li.append(...kids[0].childNodes); li.append(...kids.slice(1)); }
          else li.append(...kids);
          list.append(li);
          while (i < lines.length && !lines[i].trim() && i + 1 < lines.length && MARKER.test(lines[i + 1]) && indentOf(lines[i + 1]) === n) i++;
        }
        out.push(at(list, start));
      } else {
        const buf = [];
        while (i < lines.length && lines[i].trim() && (i === start || !startsBlock(lines, i))) buf.push(lines[i++].trim());
        out.push(at(inline(buf.join(' '), el('p'), ctx), start));
      }
    }
    return out;
  }

  function markdown(src, ctx = {}) {
    const frag = document.createDocumentFragment();
    frag.append(...blocks(src.replace(/\r\n?/g, '\n').split('\n'), ctx, ctx.lines ? 1 : 0));
    return frag;
  }

  window.BoardRender = { el, linkify, markdown };
})();

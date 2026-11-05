// The playground's editor: CodeMirror 6 on the language server that
// `stitchwort lsp` is (crates/lsp, run in lsp-worker.js), through
// @codemirror/lsp-client. docs/proposals/playground-editor.md has the design.
//
// The page (web/index.html) sees an `Editor`, which looks like a textarea
// where the page needs one: `value`, `selectionStart`, `setSelectionRange`,
// `focus`. What the page does with files, tabs and the output pane stays in
// the page; the editor owns the text on show, the colours (from the page's
// tokenizer), and everything the language server offers: errors underlined
// with their messages, hover, go to definition (into other files of a
// project and into the library, read-only), find references, formatting,
// completion, signature help, semantic colours, inlay hints on `let`s, and code actions (a proof for a `?`, an `import` for an unknown
// name), for which the client has no UI.
import { EditorView, keymap, lineNumbers, drawSelection, Decoration, WidgetType } from "@codemirror/view";
import { EditorState, StateField, StateEffect, RangeSetBuilder, Prec } from "@codemirror/state";
import { defaultKeymap, history, historyKeymap } from "@codemirror/commands";
import { indentUnit } from "@codemirror/language";
import { lintGutter } from "@codemirror/lint";
import { LSPClient, LSPPlugin, languageServerExtensions, jumpToDefinition, formatDocument } from "@codemirror/lsp-client";

/** The prefix of the library's documents: `stitchwort-std:Std/List.sw`. */
const STD = "stitchwort-std:";
/** The document of a program that isn't a file of a project. */
export const SINGLE_URI = "file:///playground/main.sw";

/**
 * Marks the text with the page's tokenizer: `colour(text, mark)` calls
 * `mark(kind, from, to)` for each stretch, in order, and a stretch gets the
 * class `hl-KIND`, which the page's CSS colours.
 */
function colouring(colour) {
  const marks = new Map();
  const mark = (kind) => marks.get(kind) ?? marks.set(kind, Decoration.mark({ class: `hl-${kind}` })).get(kind);
  const build = (text) => {
    const builder = new RangeSetBuilder();
    colour(text, (kind, from, to) => builder.add(from, to, mark(kind)));
    return builder.finish();
  };
  return StateField.define({
    create: (state) => build(state.doc.toString()),
    update: (value, tr) => (tr.docChanged ? build(tr.newDoc.toString()) : value),
    provide: (field) => EditorView.decorations.from(field),
  });
}

/** The semantic colours and inlay hints the server last gave a document (the client has neither). */
const setMarks = StateEffect.define();

class Hint extends WidgetType {
  constructor(label) { super(); this.label = label; }
  eq(other) { return other.label === this.label; }
  toDOM() {
    const span = document.createElement("span");
    span.className = "cm-inlay";
    span.textContent = this.label;
    return span;
  }
  ignoreEvent() { return true; }
}

/**
 * The decorations of the server's semantic tokens (class `sem-TYPE`, and
 * `sem-decl` on a declaration) and of its inlay hints, kept in place across
 * edits until the server answers again.
 */
function serverMarks() {
  return Prec.high(StateField.define({
    create: () => Decoration.none,
    update(value, tr) {
      value = value.map(tr.changes);
      for (const e of tr.effects) if (e.is(setMarks)) value = e.value;
      return value;
    },
    provide: (field) => EditorView.decorations.from(field),
  }));
}

export class Editor {
  /**
   * @param {Element} parent where the editor goes
   * @param {object} options
   *   colour(text, mark)          the page's tokenizer
   *   worker                      URL of lsp-worker.js
   *   module, load                the compiled WebAssembly, and the query string for files it fetches
   *   onInput()                   the text changed (by typing, a format, a code action; not by `value =`)
   *   onFile(path)                a jump to a file of the project: the page opens it (and calls `open`)
   *   onStd(path | null)          a library file is shown, or the user's text is back
   *   onNotice(text)              something to tell the person (a search is running, a request failed)
   *   run()                       Ctrl+Enter
   *   format()                    Shift+Alt+F: when given, instead of the server's formatting
   */
  constructor(parent, options) {
    this.options = options;
    this.parent = parent;
    this.path = null;
    this.backs = [];
    // One view for each document that has been shown, only the one on show
    // visible: a document stays open on the server while its tab is out of
    // sight (the project's checking goes on, and its edits are kept).
    this.views = new Map();
    this.user = null; // the user's own document on show (a view)
    this.shown = null; // what is on show: that, or a library file
    this.std = null;
    this.stdViews = new Map();
    this.stdTexts = new Map();
    this.stdWaiting = new Map();
    this.silent = 0;
    this.stats = { ready: null, crashed: null, restarts: 0, published: [], isolated: false, firstDiagnostics: null, ticks: 0, idle: false };
    this.projects = [];
    /** The diagnostics the server last published for each document, by uri. */
    this.published = new Map();
    /** The version of each document that the server says it has checked what is on show for (`stitchwort/checked`). */
    this.checkedVersions = new Map();
    this.focused = [];
    this.t0 = performance.now();
    this.handlers = [];
    this.colourField = colouring(options.colour);
    this.startWorker();
    this.client = new LSPClient({ extensions: languageServerExtensions(), timeout: 60000 }).connect(this.transport());
    this.client.workspace.displayFile = (uri) => this.displayFile(uri);
    this.open({ uri: SINGLE_URI, text: "" });
    window.addEventListener("keydown", (e) => this.setMod(e));
    window.addEventListener("keyup", (e) => this.setMod(e));
    window.addEventListener("blur", () => this.view.dom.classList.remove("mod"));
  }

  // ---- The server ----------------------------------------------------------

  startWorker() {
    const { options, stats } = this;
    // Where a page can't start workers the editor still edits, without the server.
    let worker;
    try {
      worker = this.worker = new Worker(options.worker, { type: "module" });
    } catch (e) {
      stats.crashed = String(e);
      stats.stopped = true;
      this.worker = { postMessage() {} };
      return;
    }
    worker.onerror = (e) => {
      e.preventDefault();
      stats.crashed = e.message || "the worker failed";
      stats.stopped = true;
    };
    worker.postMessage({ init: { module: options.module, load: options.load } });
    worker.onmessage = ({ data }) => {
      const now = performance.now() - this.t0;
      if (data.lsp !== undefined) {
        const m = JSON.parse(data.lsp);
        this.log("in", m, data.lsp.length);
        if (m.method === "textDocument/publishDiagnostics") {
          stats.published.push({ t: now, uri: m.params.uri, count: m.params.diagnostics.length });
          if (stats.published.length > 300) stats.published.shift();
          stats.firstDiagnostics ??= now;
          this.published.set(m.params.uri, m.params.diagnostics);
          this.scheduleMarks(m.params.uri);
        } else if (m.method === "stitchwort/checked") {
          for (const [uri, version] of Object.entries(m.params.versions)) this.checkedVersions.set(uri, version);
        }
        for (const h of this.handlers) h(data.lsp);
      } else if (data.tick !== undefined) {
        // `idle`: the server's background work (checking the rest of a project) is done, until the next message.
        stats.ticks++;
        stats.longestTick = Math.max(stats.longestTick ?? 0, data.tick);
        stats.idle = !data.more;
      } else if (data.received !== undefined) {
        stats.idle = false;
      } else if (data.ready !== undefined) {
        stats.ready = now;
      } else if (data.libraryCache !== undefined) {
        stats.libraryCache = data.libraryCache;
        stats.libraryCacheMs = data.after;
      } else if (data.stdSource !== undefined) {
        this.stdWaiting.get(data.stdSource)?.(data.text);
        this.stdWaiting.delete(data.stdSource);
      } else if (data.crashed !== undefined) {
        this.restart(data.crashed);
      } else if (data.searchCrashed !== undefined) {
        console.error("A proof search crashed:", data.searchCrashed);
      }
    };
    // Cancellation (docs/proposals/playground-editor.md §5.2.2): in a
    // cross-origin isolated page, a counter in shared memory that is bumped
    // for each edit, which the checker reads as it works and so stops a check
    // the edit has made stale. Without isolation a check runs to its end.
    this.edits = globalThis.crossOriginIsolated ? new Int32Array(new SharedArrayBuffer(4)) : null;
    if (this.edits) worker.postMessage({ edits: this.edits });
    stats.isolated = !!this.edits;
  }

  /**
   * After a crash the worker's instance can't be trusted: a new worker takes
   * over, given the projects again, and the client opens its documents in it.
   */
  restart(reason) {
    const { stats, options } = this;
    stats.crashed = reason;
    console.error("The language server crashed:", reason);
    if (++stats.restarts > 3) {
      stats.stopped = true;
      options.onNotice?.(`The language server crashed: ${reason}`);
      return;
    }
    this.worker.onmessage = null;
    this.worker.terminate?.();
    this.checkedVersions.clear();
    this.client.disconnect();
    this.startWorker();
    for (const project of this.projects) this.worker.postMessage({ project });
    this.client.connect(this.transport());
    if (this.focused.length) this.checkFirst(this.focused);
    options.onNotice?.("The language server crashed and was restarted");
  }

  /** Keeps the last few hundred messages with their times (for tests and for finding out why the server was slow). */
  log(dir, m, size) {
    const log = (this.stats.log ??= []);
    log.push({ t: Math.round(performance.now() - this.t0), dir, method: m.method, id: m.id, size, uri: m.params?.textDocument?.uri, version: m.params?.version ?? m.params?.textDocument?.version });
    if (log.length > 400) log.shift();
  }

  transport() {
    const stale = new Set(["textDocument/didChange", "textDocument/didClose"]);
    return {
      send: (message) => {
        const m = JSON.parse(message);
        this.log("out", m, message.length);
        if (this.edits && stale.has(m.method)) Atomics.add(this.edits, 0, 1);
        this.worker.postMessage(message);
      },
      subscribe: (h) => { this.handlers.push(h); },
      unsubscribe: (h) => { this.handlers = this.handlers.filter((x) => x !== h); },
    };
  }

  /** Gives the server a project (see `LanguageServer::add_project`); documents under `root` are then files of it. */
  addProject({ root, sources, paths, texts }) {
    const project = { root, sources, paths, texts };
    this.projects.push(project);
    this.worker.postMessage({ project });
  }

  /**
   * Asks the server to check the namespaces of these documents (their
   * URIs) next, along with the one being edited, and to publish their
   * diagnostics as it does: the files of the day on show, which are
   * opened in the editor one at a time. Replaces the last list.
   */
  checkFirst(uris) {
    this.focused = uris;
    this.client.notification("stitchwort/focus", { uris });
  }

  /** The diagnostics the server last published for `uri` (LSP's), or `null` if none yet. */
  diagnosticsOf(uri) {
    return this.published.get(uri) ?? null;
  }

  /**
   * Resolves when the server has checked the text of `uri` as it is now (an
   * edit not sent yet is sent first), and what the page asked it to check
   * with it (`focus`), and published the diagnostics: to `true`, or to
   * `false` if the server has stopped.
   */
  settled(uri) {
    this.client.sync();
    return new Promise((resolve) => {
      const check = () => {
        if (this.stats.stopped) return resolve(false);
        const sent = this.client.workspace.getFile(uri);
        if (sent && this.checkedVersions.get(uri) === sent.version) return resolve(true);
        setTimeout(check, 30);
      };
      check();
    });
  }

  // ---- States --------------------------------------------------------------

  /** The view on show: the user's document, or the library file. */
  get view() { return this.shown; }

  /** A state for the document `uri` with `text`. */
  stateFor(uri, text, { readOnly = false } = {}) {
    const { options } = this;
    const input = EditorView.updateListener.of((u) => {
      if (u.docChanged && !this.silent && !readOnly) options.onInput?.();
      // A jump within the file leaves a way back.
      if (u.transactions.some((tr) => tr.isUserEvent("select.definition"))) {
        if (this.skipBack) this.skipBack = false;
        else this.pushBack(u.startState);
      }
    });
    return EditorState.create({
      doc: text,
      extensions: [
        lineNumbers(), drawSelection(), history(), lintGutter(),
        indentUnit.of("  "), EditorState.tabSize.of(2),
        this.colourField,
        serverMarks(),
        client_plugin(this.client, uri),
        input,
        EditorState.readOnly.of(readOnly),
        Prec.highest(keymap.of([
          // Ctrl+Enter, and Cmd+Enter on a Mac, run the program.
          { key: "Ctrl-Enter", run: () => !!options.run?.(), preventDefault: true },
          { key: "Cmd-Enter", run: () => !!options.run?.(), preventDefault: true },
          { key: "Mod-.", run: (view) => { this.codeAction(view); return true; } },
          { key: "Mod-[", run: () => { this.goBack(); return true; } },
          { key: "Escape", run: () => { if (!this.std) return false; this.goBack(); return true; } },
          { key: "F12", run: jumpToDefinition, preventDefault: true },
          // Two spaces, as typing: undo takes it back with the text typed before it.
          { key: "Tab", run: (view) => { view.dispatch({ ...view.state.replaceSelection("  "), userEvent: "input.type" }); return true; } },
        ])),
        keymap.of([...defaultKeymap, ...historyKeymap]),
        EditorView.domEventHandlers({
          // Shift+Alt+F by its key's place (`code`): on a Mac Option+F types a character
          // for `key`, which no key binding of the client's would match.
          keydown: (e, view) => {
            if (e.code !== "KeyF" || !e.shiftKey || !e.altKey || e.ctrlKey || e.metaKey) return false;
            e.preventDefault();
            this.format(view);
            return true;
          },
          // Cmd/Ctrl-click goes to the definition, as in an editor.
          mousedown: (e, view) => {
            if (e.button !== 0 || !(e.metaKey || e.ctrlKey)) return false;
            const pos = view.posAtCoords({ x: e.clientX, y: e.clientY });
            if (pos === null) return false;
            e.preventDefault();
            view.focus();
            view.dispatch({ selection: { anchor: pos } });
            jumpToDefinition(view);
            return true;
          },
        }),
      ],
    });
  }

  setMod(e) {
    this.view.dom.classList.toggle("mod", e.metaKey || e.ctrlKey);
  }

  /** Puts `view` on show, and the others out of sight. */
  show(view) {
    if (this.shown === view) return;
    const height = this.shown?.dom.style.height;
    const focused = this.shown?.hasFocus;
    for (const v of [...this.views.values(), ...this.stdViews.values()]) v.dom.style.display = v === view ? "" : "none";
    if (height) view.dom.style.height = height;
    this.shown = view;
    view.requestMeasure();
    if (focused) view.focus();
  }

  /** Makes a view for `uri`, hidden. */
  makeView(uri, text, options) {
    const view = new EditorView({ parent: this.parent, state: this.stateFor(uri, text, options) });
    view.dom.style.display = "none";
    return view;
  }

  /** The project a document belongs to (`file:///playground/aoc/`), "" for a program on its own. */
  static group(uri) {
    return uri.match(/^file:\/\/\/playground\/[^/]+\//)?.[0] ?? "";
  }

  // ---- What the page uses, as a textarea's -----------------------------------

  /** The user's text, even while a library file is shown. */
  get value() {
    return this.user.state.doc.toString();
  }

  /** Replaces the whole text (the caret goes to its end). Not reported by `onInput`. */
  set value(text) {
    this.exitStd();
    this.silent++;
    try {
      this.user.dispatch({ changes: { from: 0, to: this.user.state.doc.length, insert: text }, selection: { anchor: text.length } });
    } finally {
      this.silent--;
    }
  }

  /** Replaces the whole text as a paste would: `onInput` is told, and undo can take it back. */
  setText(text) {
    this.exitStd();
    this.user.dispatch({ changes: { from: 0, to: this.user.state.doc.length, insert: text }, selection: { anchor: text.length }, userEvent: "input.paste" });
  }

  get selectionStart() { return this.view.state.selection.main.from; }
  get selectionEnd() { return this.view.state.selection.main.to; }
  get readOnly() { return !!this.std; }
  get scrollTop() { return this.view.scrollDOM.scrollTop; }
  set scrollTop(v) { this.view.scrollDOM.scrollTop = v; }
  get scrollLeft() { return this.view.scrollDOM.scrollLeft; }
  set scrollLeft(v) { this.view.scrollDOM.scrollLeft = v; }

  setSelectionRange(anchor, head) {
    const length = this.view.state.doc.length;
    this.view.dispatch({ selection: { anchor: Math.min(anchor, length), head: Math.min(head, length) } });
  }
  select() { this.setSelectionRange(0, this.view.state.doc.length); }
  focus(options) { this.view.focus(); if (options?.preventScroll === false) this.scrollToCaret(); }

  /** Selects from..to and scrolls it into view, near the middle. */
  reveal(from, to = from) {
    const length = this.view.state.doc.length;
    this.view.dispatch({
      selection: { anchor: Math.min(from, length), head: Math.min(to, length) },
      effects: EditorView.scrollIntoView(Math.min(from, length), { y: "center" }),
    });
  }
  /** Scrolls `offset` into view without moving the caret. */
  scrollTo(offset) { this.view.dispatch({ effects: EditorView.scrollIntoView(offset, { y: "center" }) }); }
  scrollToCaret() { this.view.dispatch({ effects: EditorView.scrollIntoView(this.view.state.selection.main.head) }); }

  /** Where the character at `offset` is drawn: the middle of its box in the viewport, or null if it isn't drawn. */
  coords(offset) {
    const r = this.view.coordsAtPos(offset);
    const next = this.view.coordsAtPos(Math.min(offset + 1, this.view.state.doc.length));
    if (!r) return null;
    const right = next && next.top === r.top ? next.left : r.left + 4;
    return { x: (r.left + right) / 2, y: (r.top + r.bottom) / 2 };
  }

  /** The coloured stretches of the text on show, by kind: { keyword: ["def", …], … } (for tests). */
  marked() {
    const out = {};
    const doc = this.view.state.doc;
    for (const it = this.view.state.field(this.colourField).iter(); it.value; it.next()) {
      (out[it.value.spec.class.slice(3)] ??= []).push(doc.sliceString(it.from, it.to));
    }
    return out;
  }

  /** The line and column (from 0, UTF-16 units) of an offset. */
  position(offset) {
    const line = this.view.state.doc.lineAt(offset);
    return [line.number - 1, offset - line.from];
  }
  /** The offset of a line and column (from 0), clamped to the text. */
  offset(line, column) {
    const doc = this.view.state.doc;
    const l = doc.line(Math.min(line + 1, doc.lines));
    return Math.min(l.from + column, l.to);
  }

  /**
   * Shows the document `uri` with `text`, as the file `path` of the project
   * (null for a program on its own). A document shown before keeps its
   * caret, scrolling and undo history, and takes `text` only if it differs;
   * a program on its own, or `fresh`, starts afresh. Any library file on
   * show is left. `restore` is { anchor, head, top, left } (see `snapshot`)
   * for a document that is new.
   */
  open({ uri, path = null, text, restore, fresh = uri === SINGLE_URI }) {
    this.exitStd();
    this.path = path;
    // Documents of another project (or of none) are closed.
    const group = Editor.group(uri);
    for (const [other, view] of this.views) {
      if (Editor.group(other) !== group) {
        view.destroy();
        this.views.delete(other);
      }
    }
    let view = this.views.get(uri);
    this.silent++;
    try {
      if (view && fresh) {
        view.setState(this.stateFor(uri, text));
      } else if (view) {
        if (view.state.doc.toString() !== text) {
          view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text }, selection: { anchor: 0 } });
        }
      } else {
        view = this.makeView(uri, text);
        this.views.set(uri, view);
        if (restore) {
          const length = text.length;
          view.dispatch({ selection: { anchor: Math.min(restore.anchor, length), head: Math.min(restore.head, length) } });
        }
      }
    } finally {
      this.silent--;
    }
    this.user = view;
    this.show(view);
    if (restore && !fresh) {
      view.requestMeasure({ read: () => null, write: () => { view.scrollDOM.scrollTop = restore.top; view.scrollDOM.scrollLeft = restore.left; } });
    }
  }

  /** Gives a document that is open (shown before) this text, if it has other. */
  update(uri, text) {
    const view = this.views.get(uri);
    if (!view || view.state.doc.toString() === text) return;
    this.silent++;
    try {
      view.dispatch({ changes: { from: 0, to: view.state.doc.length, insert: text }, selection: { anchor: 0 } });
    } finally {
      this.silent--;
    }
  }

  /** Where the caret and scrolling are, for `open`'s `restore`. */
  snapshot() {
    const s = this.user.state.selection.main;
    return { anchor: s.anchor, head: s.head, top: this.user.scrollDOM.scrollTop, left: this.user.scrollDOM.scrollLeft };
  }

  // ---- The library ---------------------------------------------------------

  get inStd() { return !!this.std; }

  /** The library file's text, from the server's WebAssembly. */
  stdText(path) {
    if (!this.stdTexts.has(path)) {
      this.stdTexts.set(path, new Promise((ok) => {
        this.stdWaiting.set(path, ok);
        this.worker.postMessage({ stdSource: path });
      }));
    }
    return this.stdTexts.get(path);
  }

  /** Shows a library file read-only, in the editor's place; `exitStd` puts the user's text back. */
  async showStd(path) {
    const text = await this.stdText(path);
    if (!text) return null;
    let view = this.stdViews.get(path);
    if (!view) {
      view = this.makeView(STD + path, text, { readOnly: true });
      this.stdViews.set(path, view);
    }
    this.std = path;
    this.show(view);
    this.options.onStd?.(path);
    return view;
  }

  exitStd() {
    if (!this.std) return;
    this.std = null;
    this.show(this.user);
    // Library files are closed on leaving (they are cheap to open again).
    for (const view of this.stdViews.values()) view.destroy();
    this.stdViews.clear();
    this.options.onStd?.(null);
  }

  // ---- Going to places -----------------------------------------------------

  /** Called by the client when it needs another file in front of the person. */
  async displayFile(uri) {
    const known = this.client.workspace.getFile(uri);
    if (known && known.getView() === this.view) return this.view;
    this.pushBack(this.view.state);
    this.skipBack = true;
    let view = null;
    if (uri.startsWith(STD)) view = await this.showStd(uri.slice(STD.length));
    else if (Editor.group(uri)) view = this.options.onFile?.(uri.slice(Editor.group(uri).length)) ? this.view : null;
    if (!view) {
      this.backs.pop();
      this.skipBack = false;
    }
    return view;
  }

  /** Remembers where the editor is, to come back to. */
  pushBack(state) {
    this.backs.push({
      std: this.std, path: this.path, anchor: state.selection.main.anchor, head: state.selection.main.head,
      top: this.scrollTop, left: this.scrollLeft,
    });
    if (this.backs.length > 50) this.backs.shift();
  }

  /** Back to where the last jump was made from: a file of the project or of the library. */
  async goBack() {
    const there = this.backs.pop();
    if (!there) {
      this.exitStd();
      return;
    }
    if (there.std) {
      await this.showStd(there.std);
    } else {
      this.exitStd();
      if (there.path !== this.path && there.path !== null) this.options.onFile?.(there.path);
    }
    this.view.focus();
    const length = this.view.state.doc.length;
    this.view.dispatch({ selection: { anchor: Math.min(there.anchor, length), head: Math.min(there.head, length) } });
    this.view.scrollDOM.scrollTop = there.top;
    this.view.scrollDOM.scrollLeft = there.left;
  }

  // ---- Semantic colours and inlay hints -----------------------------------------

  /** Asks the server for the colours and hints of `uri` soon (after a burst of answers). */
  scheduleMarks(uri) {
    this.markTimers ??= new Map();
    clearTimeout(this.markTimers.get(uri));
    this.markTimers.set(uri, setTimeout(() => this.refreshMarks(uri), 60));
  }

  async refreshMarks(uri) {
    const view = this.views.get(uri);
    const plugin = view && LSPPlugin.get(view);
    const legend = plugin?.client.serverCapabilities?.semanticTokensProvider?.legend;
    if (!plugin || !legend) return;
    const doc = view.state.doc;
    plugin.client.sync();
    const textDocument = { uri };
    const ask = (method, params) => plugin.client.request(method, params).catch(() => null);
    const [tokens, hints] = await Promise.all([
      ask("textDocument/semanticTokens/full", { textDocument }),
      ask("textDocument/inlayHint", { textDocument, range: { start: { line: 0, character: 0 }, end: plugin.toPosition(doc.length) } }),
    ]);
    // The text moved on meanwhile: the answers to the next check are for it.
    if (view.state.doc !== doc) return;
    const ranges = [];
    let line = 0, start = 0;
    for (let i = 0; tokens && i + 4 < tokens.data.length; i += 5) {
      const [dl, ds, length, type, modifiers] = tokens.data.slice(i, i + 5);
      line += dl;
      start = dl ? ds : start + ds;
      const from = plugin.fromPosition({ line, character: start });
      const classes = [`sem-${legend.tokenTypes[type]}`];
      if (modifiers & 1) classes.push("sem-decl");
      if (modifiers & 2) classes.push("sem-lib");
      ranges.push(Decoration.mark({ class: classes.join(" ") }).range(from, plugin.fromPosition({ line, character: start + length })));
    }
    for (const h of hints ?? []) {
      const label = typeof h.label === "string" ? h.label : h.label.map((p) => p.value).join("");
      ranges.push(Decoration.widget({ widget: new Hint(label), side: 1 }).range(plugin.fromPosition(h.position)));
    }
    view.dispatch({ effects: setMarks.of(Decoration.set(ranges, true)) });
  }

  // ---- Format and code actions ------------------------------------------------

  /** Formats the file: the page's `format` if it gave one, else the server's. */
  format(view = this.view) {
    if (this.std) return false;
    if (this.options.format) return this.options.format();
    return formatDocument(view);
  }

  /**
   * Code actions at the selection (the client has no UI for them): the
   * first one's edit is applied. A proof search on a `?` takes seconds, the
   * page is told meanwhile.
   */
  async codeAction(view = this.view) {
    const plugin = LSPPlugin.get(view);
    if (!plugin || this.std) return false;
    plugin.client.sync();
    const { from, to } = view.state.selection.main;
    const notice = this.options.onNotice;
    notice?.("Looking for code actions…");
    let actions;
    const start = plugin.toPosition(from);
    const end = plugin.toPosition(to);
    // The diagnostics at the cursor, which the server's quick fixes (an
    // unknown name's import) are for.
    const before = (a, b) => a.line < b.line || (a.line === b.line && a.character <= b.character);
    const diagnostics = (this.published.get(plugin.uri) ?? []).filter((d) => before(d.range.start, end) && before(start, d.range.end));
    try {
      actions = await plugin.client.request("textDocument/codeAction", {
        textDocument: { uri: plugin.uri },
        range: { start, end },
        context: { diagnostics },
      });
    } catch (e) {
      notice?.(`Code actions failed: ${e.message ?? e}`);
      return true;
    }
    const edits = actions?.[0]?.edit?.changes?.[plugin.uri];
    this.lastCodeActions = (actions ?? []).map((a) => a.title);
    if (!edits) {
      notice?.(actions?.length ? "" : "No code action here");
      return true;
    }
    notice?.(actions[0].title);
    view.dispatch({ changes: edits.map((e) => ({ from: plugin.fromPosition(e.range.start), to: plugin.fromPosition(e.range.end), insert: e.newText })) });
    return true;
  }
}

/** The client's plugin for a document of the language. */
function client_plugin(client, uri) {
  return client.plugin(uri, "stitchwort");
}

export function createEditor(parent, options) {
  return new Editor(parent, options);
}

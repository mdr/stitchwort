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
// completion, signature help, semantic colours, inlay hints on `let`s, code actions (a proof for a `?`, an `import` for an unknown
// name), for which the client has no UI, and rename (F2), whose name prompt and
// multi-file edit are here too: the client's own `renameSymbol` asks for no
// `prepareRename` and edits only the files that are open.
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

/** The line a link opened, shown with `cm-link-line` until the page's CSS has faded it, or null to take it away. */
const flashLineEffect = StateEffect.define();

function linkLine() {
  return StateField.define({
    create: () => Decoration.none,
    update(value, tr) {
      value = value.map(tr.changes);
      for (const e of tr.effects) {
        if (!e.is(flashLineEffect)) continue;
        value = e.value === null ? Decoration.none
          : Decoration.set([Decoration.line({ class: "cm-link-line" }).range(e.value)]);
      }
      return value;
    },
    provide: (field) => EditorView.decorations.from(field),
  });
}

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
   *   onCaret(uri, offset)        the caret moved or the text changed (for the page's line link)
   *   lineLink(uri, line)         the URL for a line of a project's file, or null
   *   onFile(path)                a jump to a file of the project: the page opens it (and calls `open`)
   *   onStd(path | null)          a library file is shown, or the user's text is back
   *   onGoal(answer, hide)        the goal or expected type at the caret ({goal, context, here}: the answers of `stitchwort/goalAt` and `stitchwort/contextAt`), or null when there is none; `hide` when there is no document to ask about
   *   onNotice(text)              something to tell the person (a search is running, a request failed)
   *   run()                       Ctrl+Enter
   *   save()                      Ctrl/Cmd+S: returns true when it handled the key (else the browser's save)
   *   settings                    the server's settings (crates/lsp `Settings`), sent at initialize; `configure` changes them
   *   format()                    Shift+Alt+F: when given, instead of the server's formatting
   *   fileText(path)              the text of a file of the open project (a rename edits files that aren't open), or undefined
   *   setFile(path, text)         a rename gave a file of the project this text: the page keeps it
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
    this.goalAsked = 0;
    this.stats = { ready: null, crashed: null, restarts: 0, published: [], publishedTotal: 0, isolated: false, firstDiagnostics: null, ticks: 0, idle: false };
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
    this.settings = options.settings;
    this.client = new LSPClient({ extensions: languageServerExtensions(), timeout: 300000, initializationOptions: this.settings }).connect(this.transport());
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
          // `published` keeps only a window for inspection; `publishedTotal`
          // counts every publish, so tests can tell new ones after a long check.
          stats.publishedTotal++;
          stats.published.push({ n: stats.publishedTotal, t: now, uri: m.params.uri, count: m.params.diagnostics.length });
          if (stats.published.length > 300) stats.published.shift();
          stats.firstDiagnostics ??= now;
          this.published.set(m.params.uri, m.params.diagnostics);
          this.scheduleMarks(m.params.uri);
          this.scheduleGoal(m.params.uri);
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
      } else if (data.searchWorker !== undefined) {
        stats.searchWorker = data.searchWorker;
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
    // for each document opened, changed or closed, which the checker reads as
    // it works and so stops a check the new document has made stale. Without
    // isolation a check runs to its end.
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
    const stale = new Set(["textDocument/didOpen", "textDocument/didChange", "textDocument/didClose"]);
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

  /**
   * Changes the server's settings: sent as `workspace/didChangeConfiguration`,
   * kept for a restarted server, and the colours and hints asked for again
   * (the playground's client has no server-to-client refresh).
   */
  configure(settings) {
    this.settings = settings;
    this.client.config.initializationOptions = settings;
    this.client.notification("workspace/didChangeConfiguration", { settings: { stitchwort: settings } });
    for (const uri of this.views.keys()) this.scheduleMarks(uri);
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
      if ((u.selectionSet || u.docChanged) && !readOnly && u.view === this.user) {
        this.scheduleGoal(uri);
        options.onCaret?.(uri, u.view.state.selection.main.head);
      }
      // A jump within the file leaves a way back.
      if (u.transactions.some((tr) => tr.isUserEvent("select.definition"))) {
        if (this.skipBack) this.skipBack = false;
        else this.pushBack(u.startState);
        // The client scrolls the target just into view, which in a file opened
        // by the jump is the window's bottom edge, where nothing can be hovered.
        const view = u.view;
        queueMicrotask(() => view.dispatch({ effects: EditorView.scrollIntoView(view.state.selection.main.head, { y: "center" }) }));
      }
    });
    return EditorState.create({
      doc: text,
      extensions: [
        lineNumbers(), drawSelection(), history(), lintGutter(),
        indentUnit.of("  "), EditorState.tabSize.of(2),
        this.colourField,
        serverMarks(),
        linkLine(),
        client_plugin(this.client, uri),
        input,
        EditorState.readOnly.of(readOnly),
        Prec.highest(keymap.of([
          // Ctrl+Enter, and Cmd+Enter on a Mac, run the program.
          { key: "Ctrl-Enter", run: () => !!options.run?.(), preventDefault: true },
          { key: "Cmd-Enter", run: () => !!options.run?.(), preventDefault: true },
          { key: "Mod-s", run: () => !!options.save?.() },
          { key: "Mod-.", run: (view) => { this.codeAction(view); return true; } },
          { key: "F2", run: (view) => { this.rename(view); return true; }, preventDefault: true },
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
    const uri = [...this.views].find(([, v]) => v === view)?.[0];
    if (uri) this.scheduleGoal(uri);
    else this.options.onGoal?.(null, true);
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

  /** Highlights the line at `offset` for a moment; the page's CSS fades it, or shows it plainly if motion is reduced. */
  flashLine(offset) {
    const at = this.view.state.doc.lineAt(Math.min(offset, this.view.state.doc.length)).from;
    this.view.dispatch({ effects: flashLineEffect.of(at) });
    clearTimeout(this.flashTimer);
    this.flashTimer = setTimeout(() => {
      this.view?.dispatch({ effects: flashLineEffect.of(null) });
    }, 1600);
  }

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
    this.scheduleGoal(uri);
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

  // ---- The goal at the caret -------------------------------------------------

  /** Asks for the goal at the caret of `uri` soon, after the caret or the text stops moving. */
  scheduleGoal(uri) {
    if (!this.options.onGoal || this.user !== this.views.get(uri)) return;
    clearTimeout(this.goalTimer);
    clearTimeout(this.contextTimer);
    this.goalAsked++;
    this.goalTimer = setTimeout(() => this.refreshGoal(uri), 150);
  }

  /**
   * The same requests as VS Code's Goals panel, in the same order. First
   * `stitchwort/goalAt`, answered from the goals the server last published:
   * if the caret is on a `?` that is the answer. Otherwise, once the caret
   * has rested 300 ms in all, `stitchwort/contextAt`, which checks the file
   * again, for the goal or expected type of the expression there; the
   * nearest `?` of the declaration is the fallback. The answer goes to
   * `onGoal({goal, context})` (either may be null; `goal.here` says the
   * caret is on it), or `onGoal(null)` when there is no answer, so the page
   * can keep the last one on show.
   */
  async refreshGoal(uri) {
    const view = this.views.get(uri);
    const plugin = view && LSPPlugin.get(view);
    if (!plugin || view !== this.user) return;
    if (this.shown !== view) return this.options.onGoal(null, true);
    const asked = ++this.goalAsked;
    const position = plugin.toPosition(view.state.selection.main.head);
    const params = { textDocument: { uri }, position };
    const ask = (method) => plugin.client.request(method, params).catch(() => null);
    const goal = await ask("stitchwort/goalAt");
    if (asked !== this.goalAsked) return;
    if (goal?.range && positionInRange(position, goal.range)) return this.options.onGoal({ goal, context: null, here: true });
    clearTimeout(this.contextTimer);
    this.contextTimer = setTimeout(async () => {
      const context = await ask("stitchwort/contextAt");
      if (asked !== this.goalAsked) return;
      this.options.onGoal(context || goal ? { goal, context, here: false } : null);
    }, 150);
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
    // The answers are for the text last checked, which may be shorter than this.
    const offset = ({ line, character }) => {
      const l = doc.line(Math.min(line + 1, doc.lines));
      return Math.min(l.from + character, l.to);
    };
    const ranges = [];
    let line = 0, start = 0;
    for (let i = 0; tokens && i + 4 < tokens.data.length; i += 5) {
      const [dl, ds, length, type, modifiers] = tokens.data.slice(i, i + 5);
      line += dl;
      start = dl ? ds : start + ds;
      const from = offset({ line, character: start });
      const to = offset({ line, character: start + length });
      if (to <= from) continue;
      const classes = [`sem-${legend.tokenTypes[type]}`];
      if (modifiers & 1) classes.push("sem-decl");
      if (modifiers & 2) classes.push("sem-lib");
      ranges.push(Decoration.mark({ class: classes.join(" ") }).range(from, to));
    }
    for (const h of hints ?? []) {
      const label = typeof h.label === "string" ? h.label : h.label.map((p) => p.value).join("");
      ranges.push(Decoration.widget({ widget: new Hint(label), side: 1 }).range(offset(h.position)));
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
   * Code actions at the selection (the client has no UI for them). The
   * server answers at once, from the goals the last check published (splits
   * need no search); a single plain edit is applied, anything else
   * (several actions, or "Search for a proof") is offered in a pick list,
   * with "Copy link to this line" where the page has a line link for it.
   * "Search for a proof" runs the search when it is picked (it takes
   * seconds, the page is told meanwhile) and offers the proofs found in
   * another pick list (D3519).
   */
  async codeAction(view = this.view) {
    const plugin = LSPPlugin.get(view);
    if (!plugin || this.std) return false;
    const notice = this.options.onNotice;
    // A second press while the first request runs would supersede it and
    // start the search again from nothing (loading the library is most of
    // it). The press at either side of the `?` gets the same actions, so
    // wait for the one running.
    if (this.codeActionWaiting?.has(plugin.uri)) {
      notice?.("Looking for code actions… (waiting for the one already running)");
      return true;
    }
    (this.codeActionWaiting ??= new Set()).add(plugin.uri);
    try {
      this.closePick();
      plugin.client.sync();
      // The server offers actions from the goals it last published, and a
      // project's check can take seconds: wait for the text as it is now, or
      // a `?` just typed would have no goal yet.
      notice?.("Looking for code actions… (waiting for the check)");
      if (!(await this.settled(plugin.uri))) {
        notice?.("The language server has stopped");
        return true;
      }
      const { from, to } = view.state.selection.main;
      let actions;
      const start = plugin.toPosition(from);
      const end = plugin.toPosition(to);
      // The diagnostics at the cursor, which the server's quick fixes (an
      // unknown name's import) are for.
      const before = (a, b) => a.line < b.line || (a.line === b.line && a.character <= b.character);
      const diagnostics = (this.published.get(plugin.uri) ?? []).filter((d) => before(d.range.start, end) && before(start, d.range.end));
      notice?.("Looking for code actions…");
      try {
        actions = await plugin.client.request("textDocument/codeAction", {
          textDocument: { uri: plugin.uri },
          range: { start, end },
          context: { diagnostics },
        });
      } catch (e) {
        // ContentModified: the text changed, or a newer request replaced
        // this one. That isn't "no action here"; the server says which.
        if (e.code === -32801) notice?.(e.message ?? "The text changed while looking for code actions");
        else notice?.(`Code actions failed: ${e.message ?? e}`);
        return true;
      }
      actions = actions ?? [];
      this.lastCodeActions = actions.map((a) => a.title);
      const lineLink = () => this.options.lineLink?.(plugin.uri, view.state.doc.lineAt(view.state.selection.main.head).number) ?? null;
      const copy = lineLink() === null ? null : {
        label: "Copy link to this line",
        run: async () => {
          const link = lineLink();
          if (!link) return;
          try {
            await navigator.clipboard.writeText(link);
            notice?.("Link copied");
          } catch {
            notice?.("The link is in the address bar");
          }
        },
      };
      if (!actions.length) {
        if (copy) {
          this.pick(view, "Code actions", [copy]);
          return true;
        }
        notice?.("No code action here");
        return true;
      }
      const apply = (edits, title, command) => {
        notice?.(title);
        view.dispatch({ changes: edits.map((e) => ({ from: plugin.fromPosition(e.range.start), to: plugin.fromPosition(e.range.end), insert: e.newText })) });
        // The server asks for the cursor to go to the first new `?` (D3530),
        // as a position in the text after the edit.
        const target = command?.command === "stitchwort.selectRange" ? command.arguments?.[0] : null;
        if (target) {
          const at = plugin.fromPosition(target.range.start);
          view.dispatch({ selection: { anchor: at, head: plugin.fromPosition(target.range.end) }, scrollIntoView: true });
        }
      };
      const editsOf = (a) => a.edit?.changes?.[plugin.uri];
      if (actions.length === 1 && editsOf(actions[0])) {
        apply(editsOf(actions[0]), actions[0].title, actions[0].command);
        return true;
      }
      notice?.("");
      const items = actions.map((a) => ({
        label: a.title,
        run: () => (editsOf(a) ? apply(editsOf(a), a.title, a.command) : a.command && this.searchProof(view, plugin, a.command)),
      }));
      // Last, so Enter on the list still takes the split or search the caret is on.
      if (copy) items.push(copy);
      this.pick(view, "Code actions", items);
      return true;
    } finally {
      this.codeActionWaiting.delete(plugin.uri);
    }
  }

  /**
   * The "Search for a proof" command: the server runs the search now; the
   * proofs it found are offered, best first, and the one picked replaces
   * the `?` if it is still there. A single proof is inserted at once
   * (D3532), with the cursor after it: one transaction, so undo restores
   * the `?` in one step.
   */
  async searchProof(view, plugin, command) {
    const notice = this.options.onNotice;
    // The search can take seconds (the first one in a page loads the
    // library): say it is running, and for how long.
    const began = performance.now();
    const searching = () => notice?.(`Searching for a proof… ${Math.round((performance.now() - began) / 1000)} s`);
    searching();
    const ticker = setInterval(searching, 1000);
    let answer;
    try {
      answer = await plugin.client.request("workspace/executeCommand", { command: command.command, arguments: command.arguments });
    } catch (e) {
      notice?.(e.message ?? String(e));
      return;
    } finally {
      clearInterval(ticker);
    }
    if (!answer) {
      notice?.("The text changed during the search; try again");
      return;
    }
    if (!answer.proofs.length) {
      notice?.(`No proof found within ${Math.round(answer.timeLimitMs / 100) / 10} s`);
      return;
    }
    const insert = (p, title) => {
      const from = plugin.fromPosition(answer.range.start);
      const to = plugin.fromPosition(answer.range.end);
      if (view.state.sliceDoc(from, to) !== "?") {
        notice?.("The ? has moved since the search; no proof was inserted");
        return;
      }
      notice?.(title);
      view.dispatch({ changes: { from, to, insert: p.newText }, selection: { anchor: from + p.newText.length }, scrollIntoView: true });
      view.focus();
    };
    if (answer.proofs.length === 1) {
      const [p] = answer.proofs;
      const shown = p.newText.length > 60 ? `${p.newText.slice(0, 57).trimEnd()}…` : p.newText;
      insert(p, `Proved by \`${shown}\``);
      return;
    }
    notice?.("");
    this.pick(view, "Replace ? with a proof", answer.proofs.map((p) => ({
      label: p.newText,
      detail: p.title.match(/\(([^()]*)\)$/)?.[1],
      run: () => insert(p, p.title),
    })));
  }

  /**
   * A small pick list above the editor (like the rename panel): arrow keys
   * move, Enter or a click runs the item's `run`, Escape closes it.
   */
  pick(view, title, items) {
    this.closePick();
    const panel = document.createElement("div");
    panel.className = "rename-panel pick-panel";
    panel.setAttribute("role", "listbox");
    panel.setAttribute("aria-label", title);
    const heading = Object.assign(document.createElement("div"), { textContent: title });
    panel.append(heading);
    const finish = () => { this.closePick(); view.focus(); };
    const buttons = items.map((item) => {
      const b = Object.assign(document.createElement("button"), { type: "button" });
      b.className = "pick-item";
      b.setAttribute("role", "option");
      b.append(Object.assign(document.createElement("code"), { textContent: item.label }));
      if (item.detail) b.append(" ", Object.assign(document.createElement("span"), { className: "pick-detail", textContent: item.detail }));
      b.addEventListener("click", () => { finish(); item.run(); });
      panel.append(b);
      return b;
    });
    panel.addEventListener("keydown", (e) => {
      const i = buttons.indexOf(document.activeElement);
      if (e.key === "Escape") { e.preventDefault(); finish(); }
      else if (e.key === "ArrowDown") { e.preventDefault(); buttons[(i + 1) % buttons.length].focus(); }
      else if (e.key === "ArrowUp") { e.preventDefault(); buttons[(i + buttons.length - 1) % buttons.length].focus(); }
    });
    this.parent.before(panel);
    this.pickPanel = panel;
    buttons[0]?.focus();
  }

  closePick() {
    this.pickPanel?.remove();
    this.pickPanel = null;
  }

  // ---- Rename -------------------------------------------------------------------

  /**
   * F2: asks the server whether the name at the caret can be renamed
   * (`prepareRename`), shows a prompt for the new name, and applies the
   * server's edit to every file it touches. A rename that would break
   * something is refused with the problems listed, and the prompt offers
   * "Rename anyway" (the server's `stitchwort.renameAnyway` command, which
   * answers the same edit): the person fixes the few places by hand.
   */
  async rename(view = this.view) {
    const plugin = LSPPlugin.get(view);
    if (!plugin || this.std || this.stats.stopped) return false;
    plugin.client.sync();
    const position = plugin.toPosition(view.state.selection.main.head);
    let prepared;
    try {
      prepared = await plugin.client.request("textDocument/prepareRename", { textDocument: { uri: plugin.uri }, position });
    } catch (e) {
      this.options.onNotice?.(e.message ?? String(e));
      return true;
    }
    if (!prepared?.range) {
      this.options.onNotice?.("There is no name to rename here");
      return true;
    }
    this.renamePrompt(view, plugin, position, prepared.placeholder ?? "");
    return true;
  }

  /** The small panel above the editor: the name field, the refusal's words, and "Rename anyway". */
  renamePrompt(view, plugin, position, old) {
    this.closeRename();
    const input = document.createElement("input");
    input.type = "text";
    input.name = "name";
    input.value = old;
    input.spellcheck = false;
    input.autocomplete = "off";
    input.setAttribute("aria-label", `New name for ${old}`);
    const rename = Object.assign(document.createElement("button"), { type: "submit", textContent: "Rename" });
    const cancel = Object.assign(document.createElement("button"), { type: "button", textContent: "Cancel" });
    const anyway = Object.assign(document.createElement("button"), { type: "button", textContent: "Rename anyway", hidden: true });
    anyway.className = "rename-anyway";
    const problems = document.createElement("pre");
    problems.className = "rename-problems";
    problems.hidden = true;
    problems.setAttribute("role", "alert");
    const row = document.createElement("div");
    row.className = "rename-row";
    row.append(`Rename ${old} to `, input, rename, anyway, cancel);
    const form = document.createElement("form");
    form.className = "rename-panel";
    form.append(row, problems);
    this.parent.before(form);
    this.renamePanel = form;

    const finish = () => { this.closeRename(); view.focus(); };
    const fail = (e) => {
      problems.classList.remove("busy");
      problems.textContent = e.message ?? String(e);
      problems.hidden = false;
      anyway.hidden = !e.data?.renameAnyway;
      rename.disabled = false;
      if (!anyway.hidden) anyway.focus();
    };
    const apply = async (edit) => {
      await this.applyWorkspaceEdit(edit);
      finish();
    };
    form.addEventListener("submit", async (event) => {
      event.preventDefault();
      const newName = input.value.trim();
      if (!newName || newName === old) return finish();
      rename.disabled = true;
      anyway.hidden = true;
      // The server checks the renamed project first: seconds, and on a project the size of AoC's a few minutes.
      problems.textContent = "Checking the renamed project…";
      problems.hidden = false;
      problems.classList.add("busy");
      plugin.client.sync();
      try {
        await apply(await plugin.client.request("textDocument/rename", { textDocument: { uri: plugin.uri }, position, newName }));
      } catch (e) {
        fail(e);
      }
    });
    anyway.addEventListener("click", async () => {
      anyway.disabled = true;
      try {
        await apply(await plugin.client.request("workspace/executeCommand", { command: "stitchwort.renameAnyway", arguments: [] }));
      } catch (e) {
        fail(e);
      } finally {
        anyway.disabled = false;
      }
    });
    cancel.addEventListener("click", finish);
    form.addEventListener("keydown", (e) => { if (e.key === "Escape") { e.preventDefault(); finish(); } });
    input.focus();
    input.select();
  }

  closeRename() {
    this.renamePanel?.remove();
    this.renamePanel = null;
  }

  /**
   * Applies a `WorkspaceEdit` (`changes`, or `documentChanges`) to the
   * files of the open project: an open document through its view, any other
   * file in the page's record of the project (`fileText`, `setFile`) and in
   * the worker's copy of it, which the server has not read again.
   */
  async applyWorkspaceEdit(edit) {
    const changes = edit?.changes ?? Object.fromEntries((edit?.documentChanges ?? []).map((c) => [c.textDocument.uri, c.edits]));
    const { options } = this;
    for (const [uri, edits] of Object.entries(changes)) {
      const view = this.views.get(uri);
      const group = Editor.group(uri);
      const path = uri.slice(group.length);
      if (view) {
        const plugin = LSPPlugin.get(view);
        const changes = edits.map((e) => ({ from: plugin.fromPosition(e.range.start), to: plugin.fromPosition(e.range.end), insert: e.newText }));
        this.silent++;
        try {
          view.dispatch({ changes, userEvent: "rename" });
        } finally {
          this.silent--;
        }
        if (group) options.setFile?.(path, view.state.doc.toString());
        continue;
      }
      const text = options.fileText?.(path);
      if (!group || text === undefined) continue;
      const renamed = applyTextEdits(text, edits);
      options.setFile?.(path, renamed);
      const project = this.projects.find((p) => group === `file://${p.root}/`);
      if (project) {
        const at = project.paths.indexOf(path);
        if (at >= 0) project.texts[at] = renamed;
        this.worker.postMessage({ setFile: { root: project.root, path, text: renamed } });
      }
    }
    // The page saves the open file and checks again.
    options.onInput?.();
  }
}

/** `text` with LSP `edits` applied (positions count UTF-16 units, as JavaScript strings do). */
function applyTextEdits(text, edits) {
  const starts = [0];
  for (let i = text.indexOf("\n"); i >= 0; i = text.indexOf("\n", i + 1)) starts.push(i + 1);
  const offset = ({ line, character }) => Math.min((starts[line] ?? text.length) + character, text.length);
  let out = text;
  const sorted = edits.map((e) => ({ from: offset(e.range.start), to: offset(e.range.end), insert: e.newText }))
    .sort((a, b) => b.from - a.from);
  for (const e of sorted) out = out.slice(0, e.from) + e.insert + out.slice(e.to);
  return out;
}

/** The client's plugin for a document of the language. */
function client_plugin(client, uri) {
  return client.plugin(uri, "stitchwort");
}

export function createEditor(parent, options) {
  return new Editor(parent, options);
}

/** Whether `p` is inside the LSP range `r` (ends included). */
function positionInRange(p, r) {
  return !(p.line < r.start.line || (p.line === r.start.line && p.character < r.start.character))
    && !(p.line > r.end.line || (p.line === r.end.line && p.character > r.end.character));
}

// The language server in a worker (SW-1375 trial): crates/cli/src/lsp.rs,
// compiled into the playground's WebAssembly (crates/web/src/lsp.rs). The
// page posts JSON-RPC text; the worker posts back {lsp: text} for each
// message the server sends. Between messages it runs the server's background
// work a piece at a time (one namespace's check, or one search), so a new
// edit is read before the next piece.
import init, { load_std, std_source, LanguageServer } from "../pkg/stitchwort_web.js";

let server = null;
const ready = (async () => {
  const t0 = performance.now();
  await init({ module_or_path: new URL("../pkg/stitchwort_web_bg.wasm", import.meta.url) });
  const bundle = await fetch(new URL("../pkg/std.bundle", import.meta.url)).then((r) => r.arrayBuffer());
  load_std(new Uint8Array(bundle));
  server = new LanguageServer();
  postMessage({ ready: performance.now() - t0 });
})().catch((e) => postMessage({ crashed: String(e) }));

function send(array) {
  for (const message of JSON.parse(array)) postMessage({ lsp: JSON.stringify(message) });
}

let scheduled = false;
function schedule() {
  if (scheduled) return;
  scheduled = true;
  setTimeout(tick, 0);
}

function tick() {
  scheduled = false;
  const t = performance.now();
  let answer;
  try {
    answer = JSON.parse(server.tick());
  } catch (e) {
    postMessage({ crashed: String(e) });
    return;
  }
  const ms = performance.now() - t;
  send(JSON.stringify(answer.sent));
  postMessage({ tick: ms, published: answer.sent.length, startAbs: performance.timeOrigin + t });
  if (answer.more) schedule();
}

onmessage = async ({ data }) => {
  await ready;
  if (data.stdSource !== undefined) {
    postMessage({ stdSource: data.stdSource, text: std_source(data.stdSource) });
    return;
  }
  const t = performance.now();
  try {
    send(server.receive(data));
  } catch (e) {
    postMessage({ crashed: String(e) });
    return;
  }
  postMessage({ received: performance.now() - t, method: JSON.parse(data).method });
  schedule();
};

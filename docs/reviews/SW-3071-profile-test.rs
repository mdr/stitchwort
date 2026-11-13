use std::sync::Arc;
use std::time::Instant;
use serde_json::{Value, json};
use stitchwort_lsp::{Inline, MemoryProject, Options};
use crate::common;
const STACK: usize = 256 * 1024 * 1024;

fn walk(dir: &std::path::Path, root: &std::path::Path, out: &mut std::collections::BTreeMap<String, String>) {
    for e in std::fs::read_dir(dir).unwrap() {
        let p = e.unwrap().path();
        if p.is_dir() { walk(&p, root, out); } else if let Ok(t) = std::fs::read_to_string(&p) {
            out.insert(p.strip_prefix(root).unwrap().to_string_lossy().into_owned(), t);
        }
    }
}

#[test]
#[ignore]
fn sw3071_profile() {
    std::thread::Builder::new().stack_size(STACK).spawn(body).unwrap().join().unwrap();
}

fn body() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aoc");
    let mut files = Default::default();
    for d in ["src", "inputs", "examples"] { walk(&root.join(d), &root, &mut files); }
    let day = "src/Aoc/Year2025/Day02/Day02.sw";
    let own = files[day].clone();
    let memory = Arc::new(stitchwort_lsp::Memory::default());
    memory.add(MemoryProject { root: "/memory/aoc".into(), sources: vec!["src".into()], files: Arc::new(files) });
    let mut options = Options::new(STACK);
    let log: stitchwort_driver::check_cache::StoreLog = Default::default();
    options.namespace_log = Some(log.clone());
    let bundle = common::cached_bundle(&options, STACK);
    let bundle = stitchwort_driver::check_cache::LibraryBundle::decode(&bundle).unwrap();
    options.library.set(Arc::new(bundle)).ok().unwrap();
    let mut server = Inline::new(options, memory).unwrap();
    let uri = format!("file:///memory/aoc/{day}");
    let send = |s: &mut Inline, m: Value| { s.receive(&m.to_string()); };
    send(&mut server, json!({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}));
    send(&mut server, json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}));
    let t = Instant::now();
    send(&mut server, json!({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": uri, "languageId": "stitchwort", "version": 1, "text": own}}}));
    let settle = |s: &mut Inline, what: &str| {
        use std::sync::atomic::Ordering::Relaxed;
        use stitchwort_driver::check_cache::{READ_NS, READ_BYTES};
        READ_NS.store(0, Relaxed); READ_BYTES.store(0, Relaxed);
        let t = Instant::now(); let mut ticks = 0; let mut first_pub = None; let mut tt: Vec<f64> = vec![];
        loop { let t1 = Instant::now(); let (out, more) = s.tick(); ticks += 1; tt.push(t1.elapsed().as_secs_f64());
            if first_pub.is_none() && out.iter().any(|m| m.contains("publishDiagnostics") && m.contains("Day02.sw")) { first_pub = Some(t.elapsed()); }
            if !more { break; } }
        tt.sort_by(|a, b| b.partial_cmp(a).unwrap());
        eprintln!("  store read {} ms, {} MB; slowest ticks {:?}; median tick {:.1} ms", READ_NS.load(Relaxed) / 1_000_000, READ_BYTES.load(Relaxed) / 1_000_000, &tt[..5.min(tt.len())], tt[tt.len() / 2] * 1000.0);
        eprintln!("PHASE {what}: {:?} ({ticks} ticks, edit's diagnostics at {first_pub:?})", t.elapsed());
    };
    eprintln!("open: {:?}", t.elapsed());
    settle(&mut server, "first check");
    let first = std::mem::take(&mut *log.lock().unwrap());
    eprintln!("first: {} events", first.len());
    for round in 0..3 {
        let text = if round % 2 == 0 { format!("{own}\ndef broken: Nat := rfl\n") } else { format!("{own}\n-- edit\n") };
        let tr = Instant::now();
        send(&mut server, json!({"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {"textDocument": {"uri": uri, "version": 2 + round}, "contentChanges": [{"text": text}]}}));
        eprintln!("  didChange receive: {:?}", tr.elapsed());
        settle(&mut server, &format!("re-check {round}"));
        let ev = std::mem::take(&mut *log.lock().unwrap());
        use stitchwort_driver::check_cache::StoreEvent::*;
        let c = |e| ev.iter().filter(|(_, x)| *x == e).count();
        eprintln!("re-check {round} events: found {} missing {} wrote {}", c(Found), c(Missing), c(Wrote));
    }
}

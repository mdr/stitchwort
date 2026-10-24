// Hand-written models of effect runtimes, for docs/proposals/effect-runtime-review.md.
// Throwaway code: each strategy runs the same small programs, written as the
// strategy's compiler would emit them, on JS numbers (not BigInt) and linked
// lists shaped like the generated code's. Usage:
//
//   node bench/effect-runtime/strategies.mjs [MAX_N]
//
// Strategies:
//   tree   today's runtime: Done/Call trees, `bind` rebuilds (quadratic).
//   loop   the note's design A: a `Bind` node and a run loop with an
//          immutable linked list of pending continuations; `k` resumes lazily
//          (returns a node) so handlers whose result is a computation never
//          nest JS calls.
//   fast   `loop` plus a fast path: `bind` of a finished computation calls `k`
//          directly while a depth counter allows (as js_of_ocaml and
//          cats-effect do), and builds a node otherwise.
//   cps    selective CPS with a trampoline (the shape of Links', js_of_ocaml's
//          and Effekt's JS output): effectful functions take their
//          continuation; a continuation call bounces to the trampoline every
//          100 nested calls; an operation returns {op, k} to its handler's
//          driver; handler clauses are CPS too, so `resume` is a CPS call.
//   gen    JS generators: `yield` performs, `yield*` calls; one-shot only.
//
// Programs (n elements):
//   state     mapIn (x => x + next()) under a state handler run as a loop (A′)
//   check     mapIn with a Fail-able callback that never fails (no operations)
//   ioFail    mapIn (x => print x) under a Fail handler, with print forwarded
//             through it to a top-level runner that performs it
//   search    mapIn (x => each [x]) under a collecting choice handler: n
//             forks on one path, each resumed twice (the second stops at once)
//   choices   mapIn (x => each [x, x + 10]) collected: 2^n results (n <= 16)

const MAX_N = Number(process.argv[2] ?? 1_024_000);

const Nil = { tag: "Nil" };
const cons = (head, tail) => ({ tag: "Cons", head, tail });
const range = (n) => { let l = Nil; for (let i = n - 1; i >= 0; i--) l = cons(i, l); return l; };
const sum = (l) => { let s = 0; while (l.tag === "Cons") { s += l.head; l = l.tail; } return s; };
const len = (l) => { let s = 0; while (l.tag === "Cons") { s++; l = l.tail; } return s; };
const append = (a, b) => { const xs = []; while (a.tag === "Cons") { xs.push(a.head); a = a.tail; } let r = b; for (let i = xs.length - 1; i >= 0; i--) r = cons(xs[i], r); return r; };

// ---------------------------------------------------------------- tree
const tree = (() => {
  const done = (value) => ({ tag: "Done", value });
  const call = (o, rest) => ({ tag: "Call", o, rest });
  const DONEK = done;
  const bind = (c, k) => {
    if (c.tag === "Done") return k(c.value);
    const o = c.o, r = c.rest;
    return call(o, (y) => bind(r(y), k));
  };
  const mapIn = (f, xs) => xs.tag === "Nil" ? done(Nil)
    : bind(f(xs.head), (y) => bind(mapIn(f, xs.tail), (ys) => done(cons(y, ys))));
  const op = (o) => call(o, DONEK);
  // Handlers as the elaborator writes them (folds), but the state handler as
  // a loop so that only `bind`'s cost is measured.
  const fold = (ret, clause, c) => c.tag === "Done" ? ret(c.value) : clause(c.o, (y) => fold(ret, clause, c.rest(y)));
  const state = (xs) => {
    let c = mapIn((x) => bind(op("next"), (s) => done(x + s)), xs), s = 0;
    while (c.tag === "Call") { const r = c.rest; c = r(s); s++; }
    return sum(c.value);
  };
  const failF = (x) => x < 1e9 ? done(x + 1) : op("fail");
  const toResult = (c) => fold((v) => done({ ok: v }), (o, k) => o === "fail" ? done({ err: true }) : call(o, k), c);
  const check = (xs) => { const c = toResult(mapIn(failF, xs)); return sum(c.value.ok); };
  const ioFail = (xs) => {
    const out = [];
    let c = toResult(mapIn((x) => x < 1e9 ? bind(op("print"), () => done(x)) : op("fail"), xs));
    while (c.tag === "Call") { out.push(1); c = c.rest(undefined); }
    return out.length;
  };
  const collect = (c) => fold((v) => [v], (o, k) => o === "fork" ? k(true).concat(k(false)) : [], c);
  const each1 = (x) => bind(op("fork"), (b) => b ? done(x) : op("stop"));
  const each2 = (x) => bind(op("fork"), (b) => done(b ? x : x + 10));
  const search = (xs) => collect(mapIn(each1, xs)).length;
  const choices = (xs) => collect(mapIn(each2, xs)).length;
  return { state, check, ioFail, search, choices };
})();

// ---------------------------------------------------------------- loop / fast
const makeLoop = (fastPath) => {
  const done = (value) => ({ tag: "Done", value });
  const call = (o, rest) => ({ tag: "Call", o, rest });
  let depth = 0;
  const bind = fastPath
    ? (c, k) => {
      if (c.tag === "Done" && depth < 500) { depth++; const r = k(c.value); depth--; return r; }
      return { tag: "Bind", c, k };
    }
    : (c, k) => ({ tag: "Bind", c, k });
  // Runs c with `stack` pending: the final Done, or {tag: "Op", o, rest, stack}.
  const run = (c, stack) => {
    const saved = depth; depth = 0;
    for (;;) {
      switch (c.tag) {
        case "Bind": stack = { k: c.k, next: stack }; c = c.c; break;
        case "Done":
          if (stack === null) { depth = saved; return c; }
          c = stack.k(c.value); stack = stack.next; break;
        case "Call": depth = saved; return { tag: "Op", o: c.o, rest: c.rest, stack };
      }
    }
  };
  // A deep handler. `k` is lazy: it returns a node that resumes when run.
  const fold = (ret, clause, c, stack) => {
    const r = run(c, stack);
    if (r.tag === "Done") return ret(r.value);
    const rest = r.rest, pending = r.stack;
    return clause(r.o, (y) => ({ tag: "Bind", c: done(y), k: (z) => fold(ret, clause, rest(z), pending) }));
  };
  const mapIn = (f, xs) => xs.tag === "Nil" ? done(Nil)
    : bind(f(xs.head), (y) => bind(mapIn(f, xs.tail), (ys) => done(cons(y, ys))));
  const op = (o) => call(o, done);
  const state = (xs) => {
    let r = run(mapIn((x) => bind(op("next"), (s) => done(x + s)), xs), null), s = 0;
    while (r.tag === "Op") { r = run(r.rest(s), r.stack); s++; }
    return sum(r.value);
  };
  const failF = (x) => x < 1e9 ? done(x + 1) : op("fail");
  const toResult = (c) => fold((v) => done({ ok: v }), (o, k) => o === "fail" ? done({ err: true }) : call(o, k), c, null);
  const check = (xs) => sum(run(toResult(mapIn(failF, xs)), null).value.ok);
  const ioFail = (xs) => {
    const out = [];
    let r = run(toResult(mapIn((x) => x < 1e9 ? bind(op("print"), () => done(x)) : op("fail"), xs)), null);
    while (r.tag === "Op") { out.push(1); r = run(r.rest(undefined), r.stack); }
    return out.length;
  };
  // The choice handler with its result in a computation (as `collectIn` is):
  // the clause is effectful code, so `k`'s laziness keeps it off the JS stack.
  const collect = (c) => fold((v) => done([v]),
    (o, k) => o === "fork" ? bind(k(true), (a) => bind(k(false), (b) => done(a.concat(b)))) : done([]), c, null);
  const each1 = (x) => bind(op("fork"), (b) => b ? done(x) : op("stop"));
  const each2 = (x) => bind(op("fork"), (b) => done(b ? x : x + 10));
  const search = (xs) => run(collect(mapIn(each1, xs)), null).value.length;
  const choices = (xs) => run(collect(mapIn(each2, xs)), null).value.length;
  return { state, check, ioFail, search, choices };
};
const loop = makeLoop(false);
const fast = makeLoop(true);

// ---------------------------------------------------------------- cps
const cps = (() => {
  // A step: {tag: "Done", value} | {tag: "Op", o, k} | {tag: "Bounce", k, v}.
  let depth = 0;
  const jump = (k, v) => (++depth > 100 ? (depth = 0, { tag: "Bounce", k, v }) : k(v));
  const drive = (step) => { while (step.tag === "Bounce") { depth = 0; step = step.k(step.v); } return step; };
  const start = (c) => (depth = 0, drive(c((v) => ({ tag: "Done", value: v }))));
  // Runs a continuation to its next step with a fresh count, then restores
  // the caller's, which may itself be in the middle of a chain.
  const resume = (k, y) => { const saved = depth; depth = 0; const r = drive(k(y)); depth = saved; return r; };
  // A computation is a function of its continuation.
  const done = (v) => (k) => jump(k, v);
  const bind = (c, f) => (k) => c((v) => f(v)(k));
  const op = (o) => (k) => ({ tag: "Op", o, k });
  const mapIn = (f, xs) => (k) => xs.tag === "Nil" ? jump(k, Nil)
    : f(xs.head)((y) => mapIn(f, xs.tail)((ys) => jump(k, cons(y, ys))));
  const state = (xs) => {
    let st = start(mapIn((x) => bind(op("next"), (s) => done(x + s)), xs)), s = 0;
    while (st.tag === "Op") { st = resume(st.k, s); s++; }
    return sum(st.value);
  };
  const failF = (x) => x < 1e9 ? done(x + 1) : op("fail");
  // A handler is a computation too: it drives the handled one and passes its
  // result to its own continuation `k`, forwarding other operations outwards.
  const toResult = (c) => (k) => {
    const handle = (st) => {
      if (st.tag === "Done") return jump(k, { ok: st.value });
      if (st.o === "fail") return jump(k, { err: true });
      const inner = st.k;
      return { tag: "Op", o: st.o, k: (y) => handle(resume(inner, y)) };
    };
    return handle(start(c));
  };
  const check = (xs) => sum(start(toResult(mapIn(failF, xs))).value.ok);
  const ioFail = (xs) => {
    const out = [];
    let st = start(toResult(mapIn((x) => x < 1e9 ? bind(op("print"), () => done(x)) : op("fail"), xs)));
    while (st.tag === "Op") { out.push(1); st = resume(st.k, undefined); }
    return out.length;
  };
  // Clauses in CPS: `resume` is a CPS call, so `k(true) ++ k(false)` runs on
  // the heap.
  const collect = (c) => (k) => {
    const handle = (st, k2) => {
      if (st.tag === "Done") return jump(k2, [st.value]);
      if (st.o === "stop") return jump(k2, []);
      const inner = st.k;
      const again = (y) => (k3) => jump((v) => handle(resume(inner, v), k3), y);
      return again(true)((a) => again(false)((b) => jump(k2, a.concat(b))));
    };
    return handle(start(c), k);
  };
  const each1 = (x) => bind(op("fork"), (b) => b ? done(x) : op("stop"));
  const each2 = (x) => bind(op("fork"), (b) => done(b ? x : x + 10));
  const search = (xs) => start(collect(mapIn(each1, xs))).value.length;
  const choices = (xs) => start(collect(mapIn(each2, xs))).value.length;
  return { state, check, ioFail, search, choices };
})();

// ---------------------------------------------------------------- gen
const gen = (() => {
  function* mapIn(f, xs) {
    if (xs.tag === "Nil") return Nil;
    const y = yield* f(xs.head);
    const ys = yield* mapIn(f, xs.tail);
    return cons(y, ys);
  }
  function* next(x) { return x + (yield "next"); }
  function* failF(x) { if (x < 1e9) return x + 1; yield "fail"; }
  function* print(x) { if (x < 1e9) { yield "print"; return x; } yield "fail"; }
  const state = (xs) => {
    const g = mapIn(next, xs);
    let r = g.next(), s = 0;
    while (!r.done) { r = g.next(s); s++; }
    return sum(r.value);
  };
  const check = (xs) => {
    const g = mapIn(failF, xs);
    const r = g.next();
    return r.done ? sum(r.value) : -1;
  };
  // A Fail handler as a generator that forwards other operations outwards.
  function* toResult(g) {
    let r = g.next();
    while (!r.done) {
      if (r.value === "fail") return { err: true };
      r = g.next(yield r.value);
    }
    return { ok: r.value };
  }
  const ioFail = (xs) => {
    const out = [];
    const g = toResult(mapIn(print, xs));
    let r = g.next();
    while (!r.done) { out.push(1); r = g.next(undefined); }
    return out.length;
  };
  return { state, check, ioFail };
})();

// ---------------------------------------------------------------- harness
const strategies = { tree, loop, fast, cps, gen };
const programs = ["state", "check", "ioFail", "search", "choices"];

// Agreement on small inputs.
for (const p of programs) {
  const sizes = p === "choices" ? [0, 1, 5, 10] : [0, 1, 7, 300];
  for (const n of sizes) {
    const answers = Object.entries(strategies).filter(([, s]) => s[p]).map(([name, s]) => [name, s[p](range(n))]);
    const want = answers[0][1];
    for (const [name, got] of answers) if (got !== want) console.log(`DIFFERENT ${p} ${n}: ${name} ${got} vs ${want}`);
  }
}

const time = (f, xs) => {
  const start = performance.now();
  try { f(xs); return performance.now() - start; } catch (e) {
    return e instanceof RangeError ? "stack" : `error ${e.message}`;
  }
};
const median = (xs) => xs.slice().sort((a, b) => a - b)[Math.floor(xs.length / 2)];

for (const p of programs) {
  console.log(`\n${p}`);
  const sizes = p === "choices" ? [12, 14, 16] : [1000, 4000, 16000, 64000, 256000, 1024000].filter((n) => n <= MAX_N);
  console.log(["n", ...Object.keys(strategies)].join("\t"));
  const stopped = new Set();
  for (const n of sizes) {
    const xs = range(n);
    const row = [n];
    for (const [name, s] of Object.entries(strategies)) {
      if (!s[p]) { row.push("n/a"); continue; }
      if (stopped.has(name)) { row.push(""); continue; }
      s[p](range(Math.min(n, 1000))); // warm-up
      const runs = [];
      for (let i = 0; i < 3; i++) {
        const t = time(s[p], xs);
        if (typeof t !== "number") { runs.length = 0; row.push(t); stopped.add(name); break; }
        runs.push(t);
        if (t > 3000) break;
      }
      if (runs.length) {
        const t = median(runs);
        row.push(t.toFixed(1));
        if (t > 3000) stopped.add(name);
      }
    }
    console.log(row.join("\t"));
  }
}

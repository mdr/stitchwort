//! Lookup, insert, mark and memory costs of the elaborator's table shapes:
//! a standard `HashMap` (with the elaborator's hasher), `imbl`'s and `rpds`'s
//! persistent hash maps (on `Rc`), and the undo log `nav::Logged` uses. For
//! docs/proposals/elaborator-state.md §5.2. Single-threaded, release build.

// The standard maps with `stitchwort_core::collections`' hasher are what is
// measured (the alias that crate uses is the same type).
#![allow(clippy::disallowed_types, clippy::needless_range_loop)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::collections::HashMap;
use std::hash::{BuildHasherDefault, Hasher};
use std::hint::black_box;
use std::sync::atomic::{AtomicIsize, Ordering};
use std::time::Instant;

use archery::RcK;

// ---- a live-bytes counting allocator ----

struct Counting;
static LIVE: AtomicIsize = AtomicIsize::new(0);

unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, l: Layout) -> *mut u8 {
        LIVE.fetch_add(l.size() as isize, Ordering::Relaxed);
        unsafe { System.alloc(l) }
    }
    unsafe fn dealloc(&self, p: *mut u8, l: Layout) {
        LIVE.fetch_sub(l.size() as isize, Ordering::Relaxed);
        unsafe { System.dealloc(p, l) }
    }
    unsafe fn realloc(&self, p: *mut u8, l: Layout, n: usize) -> *mut u8 {
        LIVE.fetch_add(n as isize - l.size() as isize, Ordering::Relaxed);
        unsafe { System.realloc(p, l, n) }
    }
}

#[global_allocator]
static A: Counting = Counting;

fn live() -> isize {
    LIVE.load(Ordering::Relaxed)
}

// ---- stitchwort_core::collections's hasher ----

#[derive(Default, Clone, Copy)]
struct Quick(u64);
impl Quick {
    fn add(&mut self, w: u64) {
        self.0 = (self.0.rotate_left(5) ^ w).wrapping_mul(0x51_7c_c1_b7_27_22_0a_95);
    }
}
impl Hasher for Quick {
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut w = [0u8; 8];
            w[..c.len()].copy_from_slice(c);
            self.add(u64::from_le_bytes(w));
        }
    }
    fn write_u8(&mut self, n: u8) {
        self.add(n.into())
    }
    fn write_u32(&mut self, n: u32) {
        self.add(n.into())
    }
    fn write_u64(&mut self, n: u64) {
        self.add(n)
    }
    fn write_usize(&mut self, n: usize) {
        self.add(n as u64)
    }
    fn finish(&self) -> u64 {
        self.0
    }
}
type Fixed = BuildHasherDefault<Quick>;

type Std = HashMap<String, Val, Fixed>;
type Imbl = imbl::GenericHashMap<String, Val, Fixed, RcK>;
type Rpds = rpds::HashTrieMap<String, Val, RcK, Fixed>;
type ImblVec = imbl::GenericVector<Def, RcK>;

/// A scope entry's value: `(Global, Span)`.
#[derive(Clone, Copy)]
#[allow(dead_code)]
struct Val {
    global: u64,
    file: u32,
    start: u32,
    end: u32,
}

/// Stands for a `Def` row: 96 bytes, mostly pointers.
#[derive(Clone)]
#[allow(dead_code)]
struct Def {
    words: [u64; 12],
}

fn key(i: usize) -> String {
    // Shaped like the scope's keys: `Aoc.Year2024.Day06.Proofs.lemma123`.
    format!("Aoc.Year20{}.Day{:02}.Proofs.lemma{i}", 21 + i % 5, i % 25)
}

fn val(i: usize) -> Val {
    Val {
        global: i as u64,
        file: (i % 500) as u32,
        start: i as u32,
        end: i as u32 + 9,
    }
}

/// A fixed pseudo-random order.
fn shuffled(n: usize) -> Vec<usize> {
    let mut v: Vec<usize> = (0..n).collect();
    let mut s = 0x9e37_79b9_7f4a_7c15u64;
    for i in (1..n).rev() {
        s ^= s << 13;
        s ^= s >> 7;
        s ^= s << 17;
        v.swap(i, (s % (i as u64 + 1)) as usize);
    }
    v
}

fn ns(t: Instant, ops: usize) -> f64 {
    t.elapsed().as_nanos() as f64 / ops as f64
}

/// Best of `reps` runs of `f`, which does `ops` operations: ns per op.
fn best(reps: usize, ops: usize, mut f: impl FnMut()) -> f64 {
    (0..reps)
        .map(|_| {
            let t = Instant::now();
            f();
            ns(t, ops)
        })
        .fold(f64::INFINITY, f64::min)
}

trait Map: Clone {
    fn empty() -> Self;
    fn put(&mut self, k: String, v: Val);
    fn find(&self, k: &str) -> Option<&Val>;
}
impl Map for Std {
    fn empty() -> Self {
        Std::default()
    }
    fn put(&mut self, k: String, v: Val) {
        self.insert(k, v);
    }
    fn find(&self, k: &str) -> Option<&Val> {
        self.get(k)
    }
}
impl Map for Imbl {
    fn empty() -> Self {
        Imbl::with_hasher(Fixed::default())
    }
    fn put(&mut self, k: String, v: Val) {
        self.insert(k, v);
    }
    fn find(&self, k: &str) -> Option<&Val> {
        self.get(k)
    }
}
impl Map for Rpds {
    fn empty() -> Self {
        Rpds::new_with_hasher_and_ptr_kind(Fixed::default())
    }
    fn put(&mut self, k: String, v: Val) {
        self.insert_mut(k, v);
    }
    fn find(&self, k: &str) -> Option<&Val> {
        self.get(k)
    }
}

fn map_row<M: Map>(name: &str, n: usize, keys: &[String], order: &[usize], misses: &[String]) {
    // Build.
    let insert = best(3, n, || {
        let mut m = M::empty();
        for (i, k) in keys.iter().enumerate() {
            m.put(k.clone(), val(i));
        }
        black_box(&m);
    });
    // The clone of the key is part of every row above; measure it alone to
    // subtract nothing silently.
    let before = live();
    let mut m = M::empty();
    for (i, k) in keys.iter().enumerate() {
        m.put(k.clone(), val(i));
    }
    let bytes = live() - before;
    let lookups = 1_000_000;
    let hit = best(3, lookups, || {
        let mut s = 0u64;
        for j in 0..lookups {
            let k = &keys[order[j % n]];
            s = s.wrapping_add(m.find(k).map_or(0, |v| v.global));
        }
        black_box(s);
    });
    let miss = best(3, lookups, || {
        let mut s = 0usize;
        for j in 0..lookups {
            s += m.find(&misses[j % misses.len()]).is_some() as usize;
        }
        black_box(s);
    });
    // A mark: a clone of the whole table.
    let clones = if n >= 100_000 { 20 } else { 100 };
    let mark = best(3, clones, || {
        for _ in 0..clones {
            black_box(m.clone());
        }
    }) / 1000.0;
    let before = live();
    let marked = m.clone();
    let mark_bytes = live() - before;
    // Writes just after a mark: the first touch of each path copies it.
    let w = 1000;
    // The copies are made before the clock starts: only the writes count.
    let mut copies: Vec<M> = (0..3).map(|_| marked.clone()).collect();
    let after_mark = best(3, w, || {
        let mut c = copies.pop().expect("one per run");
        for j in 0..w {
            c.put(misses[j].clone(), val(j));
        }
        black_box(&c);
    });
    println!(
        "| {name} | {n} | {insert:.0} | {hit:.0} | {miss:.0} | {mark:.1} | {:.2} | {:.0} | {after_mark:.0} |",
        mark_bytes as f64 / 1e6,
        bytes as f64 / n as f64,
    );
    drop(marked);
}

/// The undo log of `nav::Logged`, keyed like the scope.
struct Logged {
    map: Std,
    undo: Vec<(String, Option<Val>)>,
    touched: std::collections::HashSet<String, Fixed>,
}
impl Logged {
    fn put(&mut self, k: String, v: Val) {
        let old = self.map.insert(k.clone(), v);
        if self.touched.insert(k.clone()) {
            self.undo.push((k, old));
        }
    }
    fn mark(&mut self) -> usize {
        self.touched.clear();
        self.undo.len()
    }
    fn rewind(&mut self, to: usize) {
        for (k, old) in self.undo.drain(to..).rev() {
            match old {
                Some(v) => self.map.insert(k, v),
                None => self.map.remove(&k),
            };
        }
        self.touched.clear();
    }
}

/// A language server's session: `steps` namespaces, each adding `n / steps`
/// names, a mark kept before each. Live bytes retained by the marks, the
/// time to take them all, and the time to rewind to the middle one.
fn lsp(n: usize, steps: usize, keys: &[String]) {
    let per = n / steps;
    // Copying marks (the scope today).
    let base = live();
    let t = Instant::now();
    let mut m = Std::default();
    let mut marks: Vec<Std> = Vec::new();
    for s in 0..steps {
        marks.push(m.clone());
        for i in s * per..(s + 1) * per {
            m.insert(keys[i].clone(), val(i));
        }
    }
    let copy_ms = t.elapsed().as_secs_f64() * 1e3;
    let copy_bytes = live() - base;
    let t = Instant::now();
    m = marks[steps / 2].clone();
    let copy_rewind = t.elapsed().as_secs_f64() * 1e3;
    black_box(&m);
    drop((m, marks));
    // Persistent marks.
    let base = live();
    let t = Instant::now();
    let mut p = Imbl::empty();
    let mut pmarks: Vec<Imbl> = Vec::new();
    for s in 0..steps {
        pmarks.push(p.clone());
        for i in s * per..(s + 1) * per {
            p.insert(keys[i].clone(), val(i));
        }
    }
    let p_ms = t.elapsed().as_secs_f64() * 1e3;
    let p_bytes = live() - base;
    let t = Instant::now();
    p = pmarks[steps / 2].clone();
    let p_rewind = t.elapsed().as_secs_f64() * 1e3;
    black_box(&p);
    drop((p, pmarks));
    // Undo log.
    let base = live();
    let t = Instant::now();
    let mut l = Logged {
        map: Std::default(),
        undo: Vec::new(),
        touched: Default::default(),
    };
    let mut lmarks = Vec::new();
    for s in 0..steps {
        lmarks.push(l.mark());
        for i in s * per..(s + 1) * per {
            l.put(keys[i].clone(), val(i));
        }
    }
    let l_ms = t.elapsed().as_secs_f64() * 1e3;
    let l_bytes = live() - base;
    let t = Instant::now();
    l.rewind(lmarks[steps / 2]);
    let l_rewind = t.elapsed().as_secs_f64() * 1e3;
    black_box(&l.map);
    drop(l);
    println!(
        "| {n} | {steps} | copy | {copy_ms:.1} | {:.1} | {copy_rewind:.2} |",
        copy_bytes as f64 / 1e6
    );
    println!(
        "| {n} | {steps} | imbl | {p_ms:.1} | {:.1} | {p_rewind:.4} |",
        p_bytes as f64 / 1e6
    );
    println!(
        "| {n} | {steps} | undo log | {l_ms:.1} | {:.1} | {l_rewind:.2} |",
        l_bytes as f64 / 1e6
    );
}

fn vec_row(n: usize) {
    let def = Def { words: [7; 12] };
    let order = shuffled(n);
    let lookups = 1_000_000;
    let push = best(3, n, || {
        let mut v = Vec::new();
        for _ in 0..n {
            v.push(def.clone());
        }
        black_box(&v);
    });
    let v: Vec<Def> = (0..n).map(|_| def.clone()).collect();
    let get = best(3, lookups, || {
        let mut s = 0u64;
        for j in 0..lookups {
            s = s.wrapping_add(v[order[j % n]].words[3]);
        }
        black_box(s);
    });
    let ipush = best(3, n, || {
        let mut v = ImblVec::new();
        for _ in 0..n {
            v.push_back(def.clone());
        }
        black_box(&v);
    });
    let iv: ImblVec = (0..n).map(|_| def.clone()).collect();
    let iget = best(3, lookups, || {
        let mut s = 0u64;
        for j in 0..lookups {
            s = s.wrapping_add(iv[order[j % n]].words[3]);
        }
        black_box(s);
    });
    println!("| {n} | {push:.1} | {get:.1} | {ipush:.1} | {iget:.1} |");
}

fn main() {
    println!("## Hash maps keyed by name (scope-like)\n");
    println!(
        "| map | rows | insert ns | hit ns | miss ns | mark (clone) µs | mark MB | bytes/row | insert after mark ns |"
    );
    println!("|---|---:|---:|---:|---:|---:|---:|---:|---:|");
    for n in [1_000, 10_000, 30_000, 100_000] {
        let keys: Vec<String> = (0..n).map(key).collect();
        let misses: Vec<String> = (n..n + 10_000).map(key).collect();
        let order = shuffled(n);
        map_row::<Std>("std HashMap", n, &keys, &order, &misses);
        map_row::<Imbl>("imbl HashMap", n, &keys, &order, &misses);
        map_row::<Rpds>("rpds HashTrieMap", n, &keys, &order, &misses);
    }
    println!("\n## A language server's marks (one per namespace, all kept)\n");
    println!("| rows | marks | how | build + marks ms | retained MB | rewind to middle ms |");
    println!("|---:|---:|---|---:|---:|---:|");
    for (n, steps) in [(30_000, 200), (100_000, 200)] {
        let keys: Vec<String> = (0..n).map(key).collect();
        lsp(n, steps, &keys);
    }
    println!("\n## Vectors indexed by id (defs-like, 96-byte rows)\n");
    println!("| rows | Vec push ns | Vec get ns | imbl Vector push ns | imbl Vector get ns |");
    println!("|---:|---:|---:|---:|---:|");
    for n in [10_000, 100_000] {
        vec_row(n);
    }
}

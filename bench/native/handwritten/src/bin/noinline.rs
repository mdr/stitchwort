// Hand translation of the Set benchmark's hot path (Std.Map.Tree insert,
// shape, rebuild, rotations) in two styles, to bound what native code buys.
//
// "uniform": what a straightforward compiler from the erased IR would emit:
//   every value is the runtime's 3-word Value (small Nat inline, constructor
//   = tag + Rc<[Value]>), Nat arithmetic overflow-checked with a bignum
//   escape, compare called through the instance dictionary (an indirect call
//   returning an Ordering constructor), reuse in place when a cell is unique.
// "typed": what a compiler that also unboxes fields by type would emit:
//   a node struct with u64 size/key, unit value erased.
//
// Usage: set <uniform|typed> <n>
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;
use std::rc::Rc;
use std::time::Instant;

// ---------- uniform representation ----------
#[allow(dead_code)]
#[derive(Clone)]
enum Value {
    Nat(u64),
    Big(Rc<Vec<u64>>), // stands in for BigUint: never built here
    Tag(u32),
    Data(u32, Rc<[Value]>),
    Fun(fn(&Value, &Value) -> Value),
}
const TIP: u32 = 0;
const BIN: u32 = 1;
const LESS: u32 = 0;
const EQUAL: u32 = 1;
const GREATER: u32 = 2;
const UNIT: u32 = 0;

#[cold]
#[inline(never)]
#[inline(never)]
fn big_add(_a: &Value, _b: &Value) -> Value {
    panic!("bignum path")
}
#[inline(never)]
fn nat_add(a: &Value, b: &Value) -> Value {
    match (a, b) {
        (Value::Nat(x), Value::Nat(y)) => match x.checked_add(*y) {
            Some(z) => Value::Nat(z),
            None => big_add(a, b),
        },
        _ => big_add(a, b),
    }
}
#[inline(never)]
fn nat_mul(a: &Value, b: &Value) -> Value {
    match (a, b) {
        (Value::Nat(x), Value::Nat(y)) => match x.checked_mul(*y) {
            Some(z) => Value::Nat(z),
            None => big_add(a, b),
        },
        _ => big_add(a, b),
    }
}
#[inline(never)]
fn nat_leq(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Nat(x), Value::Nat(y)) => x <= y,
        _ => panic!("bignum path"),
    }
}
#[inline(never)]
fn size(t: &Value) -> Value {
    match t {
        Value::Data(_, f) => f[0].clone(),
        _ => Value::Nat(0),
    }
}
#[inline(never)]
fn bin(l: Value, k: Value, v: Value, r: Value) -> Value {
    let s = nat_add(&nat_add(&size(&l), &size(&r)), &Value::Nat(1));
    Value::Data(BIN, Rc::new([s, l, k, v, r]))
}
// Reuse an emptied cell (Perceus/Lean reset-reuse): fill it in place.
#[inline(never)]
fn bin_reuse(mut cell: Rc<[Value]>, l: Value, k: Value, v: Value, r: Value) -> Value {
    let s = nat_add(&nat_add(&size(&l), &size(&r)), &Value::Nat(1));
    match Rc::get_mut(&mut cell) {
        Some(f) => {
            f[0] = s;
            f[1] = l;
            f[2] = k;
            f[3] = v;
            f[4] = r;
            Value::Data(BIN, cell)
        }
        None => Value::Data(BIN, Rc::new([s, l, k, v, r])),
    }
}
// Take a node's fields: moved out if unique (cell kept for reuse), else cloned.
#[inline(never)]
fn unpack(cell: Rc<[Value]>) -> (Option<Rc<[Value]>>, [Value; 5]) {
    let mut cell = cell;
    match Rc::get_mut(&mut cell) {
        Some(f) => {
            let t = Value::Tag(UNIT);
            let fs = [
                std::mem::replace(&mut f[0], t.clone()),
                std::mem::replace(&mut f[1], t.clone()),
                std::mem::replace(&mut f[2], t.clone()),
                std::mem::replace(&mut f[3], t.clone()),
                std::mem::replace(&mut f[4], t),
            ];
            (Some(cell), fs)
        }
        None => (None, [cell[0].clone(), cell[1].clone(), cell[2].clone(), cell[3].clone(), cell[4].clone()]),
    }
}
#[inline(never)]
fn mk(cell: Option<Rc<[Value]>>, l: Value, k: Value, v: Value, r: Value) -> Value {
    match cell {
        Some(c) => bin_reuse(c, l, k, v, r),
        None => bin(l, k, v, r),
    }
}

#[derive(Clone, Copy)]
enum Shape {
    Keep,
    SingleL,
    DoubleL,
    SingleR,
    DoubleR,
}
#[inline(never)]
fn shape(l: &Value, r: &Value) -> Shape {
    let (sl, sr) = (size(l), size(r));
    if nat_leq(&nat_add(&sl, &sr), &Value::Nat(1)) {
        Shape::Keep
    } else if nat_leq(&nat_add(&nat_mul(&sl, &Value::Nat(3)), &Value::Nat(1)), &sr) {
        match r {
            Value::Data(_, f) => {
                if nat_leq(&nat_add(&size(&f[1]), &Value::Nat(1)), &nat_mul(&size(&f[4]), &Value::Nat(2))) {
                    Shape::SingleL
                } else {
                    Shape::DoubleL
                }
            }
            _ => Shape::Keep,
        }
    } else if nat_leq(&nat_add(&nat_mul(&sr, &Value::Nat(3)), &Value::Nat(1)), &sl) {
        match l {
            Value::Data(_, f) => {
                if nat_leq(&nat_add(&size(&f[4]), &Value::Nat(1)), &nat_mul(&size(&f[1]), &Value::Nat(2))) {
                    Shape::SingleR
                } else {
                    Shape::DoubleR
                }
            }
            _ => Shape::Keep,
        }
    } else {
        Shape::Keep
    }
}
#[inline(never)]
fn single_l(l: Value, k: Value, v: Value, r: Value) -> Value {
    match r {
        Value::Data(_, c) => {
            let (cell, [_, rl, rk, rv, rr]) = unpack(c);
            let inner = bin(l, k, v, rl);
            mk(cell, inner, rk, rv, rr)
        }
        r => bin(l, k, v, r),
    }
}
#[inline(never)]
fn single_r(l: Value, k: Value, v: Value, r: Value) -> Value {
    match l {
        Value::Data(_, c) => {
            let (cell, [_, ll, lk, lv, lr]) = unpack(c);
            let inner = bin(lr, k, v, r);
            mk(cell, ll, lk, lv, inner)
        }
        l => bin(l, k, v, r),
    }
}
#[inline(never)]
fn double_l(l: Value, k: Value, v: Value, r: Value) -> Value {
    match r {
        Value::Data(_, c) => {
            let (cell, [s, rl, rk, rv, rr]) = unpack(c);
            match rl {
                Value::Data(_, c2) => {
                    let (cell2, [_, rll, rlk, rlv, rlr]) = unpack(c2);
                    let a = mk(cell2, l, k, v, rll);
                    let b = bin(rlr, rk, rv, rr);
                    mk(cell, a, rlk, rlv, b)
                }
                rl => {
                    let _ = s;
                    let r2 = mk(cell, rl, rk, rv, rr);
                    bin(l, k, v, r2)
                }
            }
        }
        r => bin(l, k, v, r),
    }
}
#[inline(never)]
fn double_r(l: Value, k: Value, v: Value, r: Value) -> Value {
    match l {
        Value::Data(_, c) => {
            let (cell, [_, ll, lk, lv, lr]) = unpack(c);
            match lr {
                Value::Data(_, c2) => {
                    let (cell2, [_, lrl, lrk, lrv, lrr]) = unpack(c2);
                    let a = bin(ll, lk, lv, lrl);
                    let b = mk(cell2, lrr, k, v, r);
                    mk(cell, a, lrk, lrv, b)
                }
                lr => {
                    let l2 = mk(cell, ll, lk, lv, lr);
                    bin(l2, k, v, r)
                }
            }
        }
        l => bin(l, k, v, r),
    }
}
#[inline(never)]
fn rebuild(cell: Option<Rc<[Value]>>, s: Shape, l: Value, k: Value, v: Value, r: Value) -> Value {
    match s {
        Shape::Keep => mk(cell, l, k, v, r),
        Shape::SingleL => single_l(l, k, v, r),
        Shape::DoubleL => double_l(l, k, v, r),
        Shape::SingleR => single_r(l, k, v, r),
        Shape::DoubleR => double_r(l, k, v, r),
    }
}
#[inline(never)]
fn nat_compare(a: &Value, b: &Value) -> Value {
    match (a, b) {
        (Value::Nat(x), Value::Nat(y)) => Value::Tag(if x == y {
            EQUAL
        } else if x <= y {
            LESS
        } else {
            GREATER
        }),
        _ => panic!("bignum path"),
    }
}
// insert x into t, comparing through the dictionary's function value.
#[inline(never)]
fn insert(dict: &Value, x: &Value, t: Value) -> Value {
    match t {
        Value::Data(_, c) => {
            let (cell, [s, l, k, v, r]) = unpack(c);
            let ord = match dict {
                Value::Fun(f) => f(x, &k),
                _ => unreachable!(),
            };
            match ord {
                Value::Tag(LESS) => {
                    let l2 = insert(dict, x, l);
                    let sh = shape(&l2, &r);
                    rebuild(cell, sh, l2, k, v, r)
                }
                Value::Tag(GREATER) => {
                    let r2 = insert(dict, x, r);
                    let sh = shape(&l, &r2);
                    rebuild(cell, sh, l, k, v, r2)
                }
                _ => match cell {
                    Some(mut c) => {
                        let f = Rc::get_mut(&mut c).unwrap();
                        f[0] = s;
                        f[1] = l;
                        f[2] = k;
                        f[3] = Value::Tag(UNIT);
                        f[4] = r;
                        Value::Data(BIN, c)
                    }
                    None => Value::Data(BIN, Rc::new([s, l, k, Value::Tag(UNIT), r])),
                },
            }
        }
        _ => Value::Data(BIN, Rc::new([Value::Nat(1), Value::Tag(TIP), x.clone(), Value::Tag(UNIT), Value::Tag(TIP)])),
    }
}

// ---------- typed representation ----------
struct Node {
    size: u64,
    left: Tree,
    key: u64,
    right: Tree,
}
type Tree = Option<Rc<Node>>;
#[inline(never)]
fn tsize(t: &Tree) -> u64 {
    t.as_ref().map_or(0, |n| n.size)
}
#[inline(never)]
fn tbin(l: Tree, key: u64, r: Tree) -> Tree {
    Some(Rc::new(Node { size: tsize(&l) + tsize(&r) + 1, left: l, key, right: r }))
}
#[inline(never)]
fn tmk(cell: Option<Rc<Node>>, l: Tree, key: u64, r: Tree) -> Tree {
    match cell {
        Some(mut c) => {
            let n = Rc::get_mut(&mut c).unwrap();
            n.size = tsize(&l) + tsize(&r) + 1;
            n.left = l;
            n.key = key;
            n.right = r;
            Some(c)
        }
        None => tbin(l, key, r),
    }
}
#[inline(never)]
fn tunpack(mut c: Rc<Node>) -> (Option<Rc<Node>>, Tree, u64, Tree) {
    match Rc::get_mut(&mut c) {
        Some(n) => {
            let (l, k, r) = (n.left.take(), n.key, n.right.take());
            (Some(c), l, k, r)
        }
        None => (None, c.left.clone(), c.key, c.right.clone()),
    }
}
#[inline(never)]
fn tbalance(cell: Option<Rc<Node>>, l: Tree, k: u64, r: Tree) -> Tree {
    let (sl, sr) = (tsize(&l), tsize(&r));
    if sl + sr <= 1 {
        tmk(cell, l, k, r)
    } else if sl * 3 + 1 <= sr {
        let rn = r.unwrap();
        let single = tsize(&rn.left) + 1 <= tsize(&rn.right) * 2;
        let (cell2, rl, rk, rr) = tunpack(rn);
        if single {
            let a = tmk(cell, l, k, rl);
            tmk(cell2, a, rk, rr)
        } else {
            let (cell3, rll, rlk, rlr) = tunpack(rl.unwrap());
            let a = tmk(cell, l, k, rll);
            let b = tmk(cell3, rlr, rk, rr);
            tmk(cell2, a, rlk, b)
        }
    } else if sr * 3 + 1 <= sl {
        let ln = l.unwrap();
        let single = tsize(&ln.right) + 1 <= tsize(&ln.left) * 2;
        let (cell2, ll, lk, lr) = tunpack(ln);
        if single {
            let b = tmk(cell, lr, k, r);
            tmk(cell2, ll, lk, b)
        } else {
            let (cell3, lrl, lrk, lrr) = tunpack(lr.unwrap());
            let a = tmk(cell3, ll, lk, lrl);
            let b = tmk(cell, lrr, k, r);
            tmk(cell2, a, lrk, b)
        }
    } else {
        tmk(cell, l, k, r)
    }
}
#[inline(never)]
fn tinsert(x: u64, t: Tree) -> Tree {
    match t {
        None => tbin(None, x, None),
        Some(c) => {
            let (cell, l, k, r) = tunpack(c);
            if x < k {
                let l2 = tinsert(x, l);
                tbalance(cell, l2, k, r)
            } else if x > k {
                let r2 = tinsert(x, r);
                tbalance(cell, l, k, r2)
            } else {
                tmk(cell, l, k, r)
            }
        }
    }
}

#[inline(never)]
fn main() {
    let args: Vec<String> = std::env::args().collect();
    let mode = args[1].as_str();
    let n: u64 = args[2].parse().unwrap();
    let t0 = Instant::now();
    let keys: Vec<u64> = (0..n).map(|i| (i * 7919) % n).collect();
    let size = match mode {
        "uniform" => {
            let dict = Value::Fun(nat_compare);
            let keys: Vec<Value> = keys.iter().map(|&k| Value::Nat(k)).collect();
            let t1 = Instant::now();
            let mut t = Value::Tag(TIP);
            for k in &keys {
                t = insert(&dict, k, t);
            }
            let s = match size(&t) {
                Value::Nat(s) => s,
                _ => 0,
            };
            eprintln!("insert {:.3}s", t1.elapsed().as_secs_f64());
            drop(t);
            s
        }
        _ => {
            let t1 = Instant::now();
            let mut t: Tree = None;
            for &k in &keys {
                t = tinsert(k, t);
            }
            let s = tsize(&t);
            eprintln!("insert {:.3}s", t1.elapsed().as_secs_f64());
            // free iteratively-ish: depth is only ~40, recursion is fine
            drop(t);
            s
        }
    };
    eprintln!("total {:.3}s", t0.elapsed().as_secs_f64());
    println!("{size}");
}

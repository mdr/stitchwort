//! The translation test oracle for nested data types
//! (docs/proposals/nested-data-types.md §8; SW-704 stage 1).
//!
//! The kernel accepts a data type inside an earlier data type at nestable
//! parameters (§5). The rule's justification is Lamiaux, Forster, Sozeau and
//! Tabareau's theorem that such a type has a strictly positive *mutual*
//! encoding: the type, with a private copy of each container it's nested in
//! (§6). This test checks that per declaration, with today's kernel, on
//! declarations made by a small generator and on seeds written by hand.
//!
//! For each case, the program is a fixed library of containers, 0-2
//! randomly generated earlier groups, and the group under test. The
//! translation (§8, LFST §3.1) is done here, on this file's own small
//! syntax tree, so it never parses: repeatedly, the first nested occurrence
//! `D σ` is replaced by a copy of `D`'s whole group with its parameters
//! replaced by `σ`, indexed by the earlier fields `σ` mentions (LFST's
//! `↑args`), until none is left. Then both programs are checked by the real
//! elaborator and kernel (`Session::load`).
//!
//! - **Property 1 (must hold):** if the nested program is accepted, its
//!   translation exists and is accepted. A failure prints both programs.
//! - **Property 2 (reported, not required):** if the translation is
//!   accepted but the nested program is refused (by `E-POSITIVITY`), the
//!   case is counted and the first few are printed. Two kinds are expected:
//!   §5.5's restriction (a parameter another parameter's type mentions isn't
//!   nestable: `ODep` below, and a generated group with a predicate on its
//!   first parameter), counted separately; and a container that doesn't use
//!   its parameter (`OPhantom`, or a generated one), whose copy loses the
//!   occurrence, so that something the rule refuses by where the type's name
//!   is written (`OPhantom (ONeg T)`) vanishes from the translation. Neither
//!   is a soundness question: the rule refuses more than it must.
//!
//! Property 3 (values: `fromMut (toMut v) = v`) isn't here yet.
//!
//! One deliberate difference from LFST's encoding: a copy is declared in the
//! group's universe, not the container's, because the members of a
//! Stitchwort group share one. For strict positivity, which is what this
//! checks, the universe makes no difference: a field's universe is checked
//! separately (`E-UNIVERSE`), and positivity reads only where the group's
//! types occur. (What a proposition may be matched to produce does depend on
//! it, which is §5.4's rule, not tested here.)
//!
//! Cases: the seeds, then generated ones up to 50 in the lane and merge
//! tiers (about 1.5 s), 400 in daily (about 12 s), 4000 in full (about
//! 3.5 minutes), each case on a pool of its own (`par_map`). `ORACLE_CASES`
//! and `ORACLE_SEED` (decimal) set others, and `ORACLE_SHOW` how many of
//! property 2's other counterexamples to print (3).

use std::collections::{BTreeMap, BTreeSet};
use std::fmt::Write as _;

use stitchwort_driver::driver::{Session, Tier, par_map, tier, with_stack};

// --- terms -------------------------------------------------------------

/// A type or term as written: a name applied to arguments (a data type, a
/// constructor, a variable, `Nat`, `Type`, `Prop`), a function type, a
/// lambda, an equation or a number.
#[derive(Clone, Debug, PartialEq)]
enum T {
    App(String, Vec<T>),
    Arrow(Box<T>, Box<T>),
    Lam(String, Box<T>),
    Eq(Box<T>, Box<T>),
    Lit(u32),
}

fn name(x: &str) -> T {
    T::App(x.to_string(), Vec::new())
}

fn app(f: &str, args: Vec<T>) -> T {
    T::App(f.to_string(), args)
}

fn arrow(a: T, b: T) -> T {
    T::Arrow(Box::new(a), Box::new(b))
}

fn lam(x: &str, body: T) -> T {
    T::Lam(x.to_string(), Box::new(body))
}

fn equal(a: T, b: T) -> T {
    T::Eq(Box::new(a), Box::new(b))
}

impl T {
    fn render(&self) -> String {
        match self {
            T::App(f, args) => {
                let mut s = f.clone();
                for a in args {
                    s.push(' ');
                    s.push_str(&a.atom());
                }
                s
            }
            T::Arrow(a, b) => format!("{} → {}", a.operand(), b.render()),
            T::Lam(x, b) => format!("{x} => {}", b.render()),
            T::Eq(a, b) => format!("{} = {}", a.operand(), b.operand()),
            T::Lit(n) => n.to_string(),
        }
    }

    /// As an argument.
    fn atom(&self) -> String {
        match self {
            T::App(_, args) if args.is_empty() => self.render(),
            T::Lit(_) => self.render(),
            _ => format!("({})", self.render()),
        }
    }

    /// Left of an arrow, or either side of `=`.
    fn operand(&self) -> String {
        match self {
            T::Arrow(..) | T::Lam(..) | T::Eq(..) => format!("({})", self.render()),
            _ => self.render(),
        }
    }

    /// Whether any name in `names` occurs (as a type, a constructor or a
    /// variable).
    fn mentions(&self, names: &BTreeSet<String>) -> bool {
        match self {
            T::App(f, args) => names.contains(f) || args.iter().any(|a| a.mentions(names)),
            T::Arrow(a, b) | T::Eq(a, b) => a.mentions(names) || b.mentions(names),
            T::Lam(_, b) => b.mentions(names),
            T::Lit(_) => false,
        }
    }

    /// The names in it, in order.
    fn names(&self, out: &mut Vec<String>) {
        match self {
            T::App(f, args) => {
                out.push(f.clone());
                args.iter().for_each(|a| a.names(out));
            }
            T::Arrow(a, b) | T::Eq(a, b) => {
                a.names(out);
                b.names(out);
            }
            T::Lam(_, b) => b.names(out),
            T::Lit(_) => {}
        }
    }

    /// Replaces names by terms, applying a substituted lambda to its
    /// arguments. Every name bound by a lambda here is fresh, so nothing is
    /// captured.
    fn subst(&self, map: &BTreeMap<String, T>) -> T {
        match self {
            T::App(f, args) => {
                let args: Vec<T> = args.iter().map(|a| a.subst(map)).collect();
                match map.get(f) {
                    Some(r) => apply(r.clone(), args),
                    None => T::App(f.clone(), args),
                }
            }
            T::Arrow(a, b) => arrow(a.subst(map), b.subst(map)),
            T::Eq(a, b) => equal(a.subst(map), b.subst(map)),
            T::Lam(x, b) => {
                let mut inner = map.clone();
                inner.remove(x);
                lam(x, b.subst(&inner))
            }
            T::Lit(_) => self.clone(),
        }
    }

    /// The first subterm (outermost first, left to right) for which `f`
    /// gives a replacement, replaced.
    fn replace_first(&self, f: &mut dyn FnMut(&T) -> Option<T>) -> Option<T> {
        if let Some(r) = f(self) {
            return Some(r);
        }
        match self {
            T::App(g, args) => (0..args.len()).find_map(|i| {
                args[i].replace_first(f).map(|r| {
                    let mut args = args.clone();
                    args[i] = r;
                    T::App(g.clone(), args)
                })
            }),
            T::Arrow(a, b) => a
                .replace_first(f)
                .map(|a| arrow(a, (**b).clone()))
                .or_else(|| b.replace_first(f).map(|b| arrow((**a).clone(), b))),
            T::Eq(a, b) => a
                .replace_first(f)
                .map(|a| equal(a, (**b).clone()))
                .or_else(|| b.replace_first(f).map(|b| equal((**a).clone(), b))),
            T::Lam(x, b) => b.replace_first(f).map(|b| lam(x, b)),
            T::Lit(_) => None,
        }
    }
}

/// `f args`, reducing a lambda applied to an argument.
fn apply(f: T, args: Vec<T>) -> T {
    args.into_iter().fold(f, |f, a| match f {
        T::Lam(x, body) => body.subst(&BTreeMap::from([(x, a)])),
        T::App(g, mut gargs) => {
            gargs.push(a);
            T::App(g, gargs)
        }
        other => panic!("can't apply {}", other.render()),
    })
}

// --- declarations ------------------------------------------------------

#[derive(Clone, Debug)]
struct Ctor {
    name: String,
    fields: Vec<(String, T)>,
    /// The result's indices (none for a member without indices).
    result: Vec<T>,
}

#[derive(Clone, Debug)]
struct Member {
    name: String,
    /// Index types, in the context of the parameters.
    indices: Vec<T>,
    ctors: Vec<Ctor>,
}

/// A data group: members sharing one parameter telescope and one universe.
#[derive(Clone, Debug)]
struct Group {
    params: Vec<(String, T)>,
    prop: bool,
    members: Vec<Member>,
}

fn ctor(name: &str, fields: Vec<(&str, T)>, result: Vec<T>) -> Ctor {
    Ctor {
        name: name.to_string(),
        fields: fields
            .into_iter()
            .map(|(x, t)| (x.to_string(), t))
            .collect(),
        result,
    }
}

fn member(name: &str, indices: Vec<T>, ctors: Vec<Ctor>) -> Member {
    Member {
        name: name.to_string(),
        indices,
        ctors,
    }
}

fn group(params: Vec<(&str, T)>, prop: bool, members: Vec<Member>) -> Group {
    Group {
        params: params
            .into_iter()
            .map(|(x, t)| (x.to_string(), t))
            .collect(),
        prop,
        members,
    }
}

impl Group {
    fn param_vars(&self) -> Vec<T> {
        self.params.iter().map(|(x, _)| name(x)).collect()
    }

    fn member_names(&self) -> BTreeSet<String> {
        self.members.iter().map(|m| m.name.clone()).collect()
    }

    fn render(&self, out: &mut String) {
        let params: String = self
            .params
            .iter()
            .map(|(x, t)| format!(" ({x}: {})", t.render()))
            .collect();
        let sort = if self.prop { "Prop" } else { "Type" };
        for m in &self.members {
            let sig: String = m
                .indices
                .iter()
                .map(|i| format!("{} → ", i.operand()))
                .collect();
            let _ = writeln!(out, "type {}{params}: {sig}{sort} =", m.name);
            for c in &m.ctors {
                let fields: String = c
                    .fields
                    .iter()
                    .map(|(x, t)| format!(" ({x}: {})", t.render()))
                    .collect();
                let result = if m.indices.is_empty() {
                    String::new()
                } else {
                    let mut args = self.param_vars();
                    args.extend(c.result.iter().cloned());
                    format!(": {}", app(&m.name, args).render())
                };
                let _ = writeln!(out, "  | {}{fields}{result}", c.name);
            }
            out.push('\n');
        }
    }
}

fn program(groups: &[&Group]) -> String {
    let mut out = String::from("import Std (Eq, Nat)\n\n");
    for g in groups {
        g.render(&mut out);
    }
    out
}

// --- the library of containers -----------------------------------------

/// The containers every case may nest in (§8), with which of their
/// parameters are nestable by §5.1, for the reader.
fn library() -> Vec<Group> {
    let a = || name("a");
    let ty = || name("Type");
    let nat = || name("Nat");
    vec![
        // `a` nestable.
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "OList",
                vec![],
                vec![
                    ctor("ONil", vec![], vec![]),
                    ctor(
                        "OCons",
                        vec![("x", a()), ("xs", app("OList", vec![a()]))],
                        vec![],
                    ),
                ],
            )],
        ),
        // `a` nestable.
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "OOpt",
                vec![],
                vec![
                    ctor("ONone", vec![], vec![]),
                    ctor("OSome", vec![("v", a())], vec![]),
                ],
            )],
        ),
        // Both nestable.
        group(
            vec![("a", ty()), ("b", ty())],
            false,
            vec![member(
                "OPair",
                vec![],
                vec![ctor("OMk", vec![("fst", a()), ("snd", name("b"))], vec![])],
            )],
        ),
        // `a` nestable; the index is a number.
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "OVec",
                vec![nat()],
                vec![
                    ctor("OVNil", vec![], vec![T::Lit(0)]),
                    ctor(
                        "OVCons",
                        vec![
                            ("k", nat()),
                            ("x", a()),
                            ("xs", app("OVec", vec![a(), name("k")])),
                        ],
                        vec![app("Succ", vec![name("k")])],
                    ),
                ],
            )],
        ),
        // A mutual group: `a` nestable.
        group(
            vec![("a", ty())],
            false,
            vec![
                member(
                    "OTree",
                    vec![],
                    vec![ctor(
                        "ONode",
                        vec![("lab", a()), ("kids", app("OForest", vec![a()]))],
                        vec![],
                    )],
                ),
                member(
                    "OForest",
                    vec![],
                    vec![
                        ctor("OFNil", vec![], vec![]),
                        ctor(
                            "OFCons",
                            vec![
                                ("first", app("OTree", vec![a()])),
                                ("rest", app("OForest", vec![a()])),
                            ],
                            vec![],
                        ),
                    ],
                ),
            ],
        ),
        // `a` is a function's input: not nestable.
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "ONeg",
                vec![],
                vec![ctor("OMkNeg", vec![("consume", arrow(a(), nat()))], vec![])],
            )],
        ),
        // `a` nestable, `b` not (an input).
        group(
            vec![("a", ty()), ("b", ty())],
            false,
            vec![member(
                "OW",
                vec![],
                vec![
                    ctor("OWLeaf", vec![], vec![]),
                    ctor(
                        "OWNode",
                        vec![
                            ("lab", a()),
                            ("sub", arrow(name("b"), app("OW", vec![a(), name("b")]))),
                        ],
                        vec![],
                    ),
                ],
            )],
        ),
        // `a` nestable (it occurs nowhere).
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "OPhantom",
                vec![],
                vec![ctor("OMkPhantom", vec![], vec![])],
            )],
        ),
        // `a` not nestable: the later parameter's type mentions it (§5.5).
        group(
            vec![("a", ty()), ("xs", app("OList", vec![a()]))],
            false,
            vec![member(
                "ODep",
                vec![],
                vec![ctor("OMkDep", vec![("y", a())], vec![])],
            )],
        ),
        // `p` nestable; `a` not (the index type mentions it).
        group(
            vec![("a", ty()), ("p", arrow(a(), name("Prop")))],
            true,
            vec![member(
                "OAll",
                vec![app("OList", vec![a()])],
                vec![
                    ctor("OAllNil", vec![], vec![name("ONil")]),
                    ctor(
                        "OAllCons",
                        vec![
                            ("x", a()),
                            ("xs", app("OList", vec![a()])),
                            ("here", app("p", vec![name("x")])),
                            ("rest", app("OAll", vec![a(), name("p"), name("xs")])),
                        ],
                        vec![app("OCons", vec![name("x"), name("xs")])],
                    ),
                ],
            )],
        ),
        // `a` not nestable: the index type is `a`.
        group(
            vec![("a", ty())],
            false,
            vec![member(
                "OIdx",
                vec![a()],
                vec![ctor("OMkIdx", vec![("x", a())], vec![name("x")])],
            )],
        ),
    ]
}

// --- the translation ---------------------------------------------------

/// Where to find each container: its group, by member name.
struct Env<'a> {
    groups: Vec<&'a Group>,
}

impl Env<'_> {
    fn group_of(&self, member: &str) -> Option<&Group> {
        self.groups
            .iter()
            .copied()
            .find(|g| g.members.iter().any(|m| m.name == member))
    }
}

/// LFST's translation of `g` (§3.1 of their paper): the group without
/// nested occurrences, its members followed by the copies (named with
/// `tag`, which tells apart the copies made for different groups); or why
/// there's none.
fn translate(env: &Env, g: &Group, tag: usize) -> Result<Group, String> {
    let mut out = g.clone();
    // Copies made so far, by container group and instance: the name of the
    // copy of each of its members.
    let mut copies: BTreeMap<String, BTreeMap<String, String>> = BTreeMap::new();
    for _ in 0..40 {
        let members = out.member_names();
        let mut found = None;
        'search: for (mi, m) in out.members.iter().enumerate() {
            for (ci, c) in m.ctors.iter().enumerate() {
                for (fi, (_, ty)) in c.fields.iter().enumerate() {
                    let mut occurrence = None;
                    ty.replace_first(&mut |t| match t {
                        T::App(d, args)
                            if !members.contains(d)
                                && env.group_of(d).is_some()
                                && args.iter().any(|a| a.mentions(&members)) =>
                        {
                            occurrence = Some(t.clone());
                            Some(t.clone())
                        }
                        _ => None,
                    });
                    if let Some(o) = occurrence {
                        found = Some((mi, ci, fi, o));
                        break 'search;
                    }
                }
            }
        }
        let Some((mi, ci, fi, occurrence)) = found else {
            return Ok(out);
        };
        let T::App(d, args) = &occurrence else {
            unreachable!()
        };
        let outer = env.group_of(d).expect("a container");
        let k = outer.params.len();
        if args[k..].iter().any(|a| a.mentions(&members)) {
            return Err(format!("a member in `{d}`'s indices"));
        }
        let sigma = &args[..k];
        // The earlier fields the instance mentions, which become indices.
        let ctor = &out.members[mi].ctors[ci];
        let earlier: BTreeSet<String> = ctor.fields[..fi].iter().map(|(x, _)| x.clone()).collect();
        let mut mentioned = Vec::new();
        sigma.iter().for_each(|s| s.names(&mut mentioned));
        let mut locals: Vec<(String, T)> = Vec::new();
        for x in mentioned {
            if earlier.contains(&x) && !locals.iter().any(|(y, _)| *y == x) {
                let ty = ctor
                    .fields
                    .iter()
                    .find(|(y, _)| *y == x)
                    .expect("a field")
                    .1
                    .clone();
                if ty.mentions(&members) {
                    return Err(format!("the instance mentions `{x}`, which holds a member"));
                }
                if ty.mentions(&earlier) {
                    return Err(format!(
                        "the instance mentions `{x}`, whose type depends on a field"
                    ));
                }
                locals.push((x, ty));
            }
        }
        let renamed: BTreeMap<String, T> = locals
            .iter()
            .enumerate()
            .map(|(j, (x, _))| (x.clone(), name(&format!("l{j}"))))
            .collect();
        let sigma_r: Vec<T> = sigma.iter().map(|s| s.subst(&renamed)).collect();
        let local_types: Vec<T> = locals.iter().map(|(_, t)| t.clone()).collect();
        let key = format!(
            "{}|{}|{}",
            outer.members[0].name,
            sigma_r.iter().map(T::render).collect::<Vec<_>>().join(", "),
            local_types
                .iter()
                .map(T::render)
                .collect::<Vec<_>>()
                .join(", "),
        );
        if !copies.contains_key(&key) {
            let n = copies.len();
            let names: BTreeMap<String, String> = outer
                .members
                .iter()
                .map(|om| (om.name.clone(), format!("K{tag}x{n}{}", om.name)))
                .collect();
            let pmap: BTreeMap<String, T> = outer
                .params
                .iter()
                .map(|(x, _)| x.clone())
                .zip(sigma_r.iter().cloned())
                .collect();
            let gparams = out.param_vars();
            let lvars: Vec<T> = (0..locals.len()).map(|j| name(&format!("l{j}"))).collect();
            let inst = |t: &T| instantiate(t, &names, k, &pmap, &gparams, &lvars);
            for om in &outer.members {
                let mut indices = local_types.clone();
                indices.extend(om.indices.iter().map(inst));
                if indices.iter().any(|i| i.mentions(&members)) {
                    return Err(format!("a member in the type of `{}`'s indices", om.name));
                }
                let ctors = om
                    .ctors
                    .iter()
                    .map(|c| {
                        let mut fields: Vec<(String, T)> = local_types
                            .iter()
                            .enumerate()
                            .map(|(j, t)| (format!("l{j}"), t.clone()))
                            .collect();
                        fields.extend(c.fields.iter().map(|(x, t)| (x.clone(), inst(t))));
                        let mut result = lvars.clone();
                        result.extend(c.result.iter().map(inst));
                        Ctor {
                            name: format!("K{tag}x{n}{}", c.name),
                            fields,
                            result,
                        }
                    })
                    .collect();
                out.members.push(Member {
                    name: names[&om.name].clone(),
                    indices,
                    ctors,
                });
            }
            copies.insert(key.clone(), names);
        }
        let copy = copies[&key][d].clone();
        let mut use_args = out.param_vars();
        use_args.extend(locals.iter().map(|(x, _)| name(x)));
        use_args.extend(args[k..].iter().cloned());
        let replacement = app(&copy, use_args);
        let field = &mut out.members[mi].ctors[ci].fields[fi].1;
        *field = field
            .replace_first(&mut |t| (*t == occurrence).then(|| replacement.clone()))
            .expect("the occurrence is there");
    }
    Err("too many copies".to_string())
}

/// `g`'s members split into the groups the elaborator makes of them: the
/// members that refer to each other, directly or through others, are one
/// group, and a group comes after the ones it refers to. Each keeps `g`'s
/// parameters and universe.
fn components(g: &Group) -> Vec<Group> {
    let n = g.members.len();
    let refers = |i: usize, j: usize| {
        let target = BTreeSet::from([g.members[j].name.clone()]);
        let m = &g.members[i];
        m.indices.iter().any(|t| t.mentions(&target))
            || m.ctors.iter().any(|c| {
                c.fields.iter().any(|(_, t)| t.mentions(&target))
                    || c.result.iter().any(|t| t.mentions(&target))
            })
    };
    // reaches[i][j]: member i refers to member j, through any others.
    let mut reaches: Vec<Vec<bool>> = (0..n)
        .map(|i| (0..n).map(|j| refers(i, j)).collect())
        .collect();
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if reaches[i][k] && reaches[k][j] {
                    reaches[i][j] = true;
                }
            }
        }
    }
    let mut placed = vec![false; n];
    let mut out = Vec::new();
    while placed.iter().any(|p| !p) {
        // A member whose own group refers to nothing still unplaced outside
        // it.
        let i = (0..n)
            .find(|&i| {
                !placed[i] && (0..n).all(|j| placed[j] || j == i || !reaches[i][j] || reaches[j][i])
            })
            .expect("a group with nothing left to wait for");
        let part: Vec<usize> = (0..n)
            .filter(|&j| !placed[j] && (j == i || (reaches[i][j] && reaches[j][i])))
            .collect();
        for &j in &part {
            placed[j] = true;
        }
        out.push(Group {
            params: g.params.clone(),
            prop: g.prop,
            members: part.iter().map(|&j| g.members[j].clone()).collect(),
        });
    }
    out
}

/// A container's term `t`, in the copy: its members (applied to its own
/// parameters, then indices) become the copies, applied to the group's
/// parameters, the locals and the indices; its parameters become the
/// instance.
fn instantiate(
    t: &T,
    names: &BTreeMap<String, String>,
    k: usize,
    pmap: &BTreeMap<String, T>,
    gparams: &[T],
    lvars: &[T],
) -> T {
    let go = |t: &T| instantiate(t, names, k, pmap, gparams, lvars);
    match t {
        T::App(f, args) if names.contains_key(f) => {
            let mut new = gparams.to_vec();
            new.extend(lvars.iter().cloned());
            new.extend(args[k..].iter().map(go));
            app(&names[f], new)
        }
        T::App(f, args) => {
            let args: Vec<T> = args.iter().map(go).collect();
            match pmap.get(f) {
                Some(r) => apply(r.clone(), args),
                None => T::App(f.clone(), args),
            }
        }
        T::Arrow(a, b) => arrow(go(a), go(b)),
        T::Eq(a, b) => equal(go(a), go(b)),
        T::Lam(x, b) => lam(x, go(b)),
        T::Lit(_) => t.clone(),
    }
}

// --- the generator -----------------------------------------------------

/// xorshift, as in `fuzz_elab.rs`.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_f491_4f6c_dd1d)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n.max(1) as u64) as usize
    }

    fn chance(&mut self, percent: usize) -> bool {
        self.below(100) < percent
    }

    fn pick<'a, U>(&mut self, xs: &'a [U]) -> &'a U {
        &xs[self.below(xs.len())]
    }
}

/// A randomly generated earlier group `R{k}`: 1-2 members, a `Type`
/// parameter and maybe a second (`Type`, or a predicate on the first), 0-1
/// number index, 1-2 constructors of 0-3 fields.
fn random_outer(rng: &mut Rng, k: usize) -> Group {
    let mut params = vec![("r0".to_string(), name("Type"))];
    let predicate = match rng.below(3) {
        0 => None,
        1 => {
            params.push(("r1".to_string(), name("Type")));
            None
        }
        _ => {
            params.push(("r1".to_string(), arrow(name("r0"), name("Prop"))));
            Some("r1")
        }
    };
    let types: Vec<&str> = params
        .iter()
        .filter(|(_, t)| *t == name("Type"))
        .map(|(x, _)| x.as_str())
        .collect();
    let count = 1 + rng.below(2);
    let names: Vec<String> = (0..count).map(|m| format!("R{k}m{m}")).collect();
    let indexed: Vec<bool> = (0..count).map(|_| rng.chance(25)).collect();
    let pvars: Vec<T> = params.iter().map(|(x, _)| name(x)).collect();
    let members = (0..count)
        .map(|m| {
            let ctors = (0..1 + rng.below(2))
                .map(|c| {
                    let mut fields: Vec<(String, T)> = Vec::new();
                    for f in 0..rng.below(4) {
                        let p = name(rng.pick(&types));
                        let sibling = rng.below(count);
                        let mut own = pvars.clone();
                        if indexed[sibling] {
                            own.push(T::Lit(0));
                        }
                        let earlier_r0 = fields
                            .iter()
                            .find(|(_, t)| *t == name("r0"))
                            .map(|(x, _)| x.clone());
                        let ty = match rng.below(9) {
                            0 => name("Nat"),
                            1 => p,
                            2 => arrow(p, name("Nat")),
                            3 => arrow(name("Nat"), p),
                            4 => app("OList", vec![p]),
                            5 => app("ONeg", vec![p]),
                            6 => app(&names[sibling], own),
                            7 => match (predicate, earlier_r0) {
                                (Some(q), Some(x)) => app(q, vec![name(&x)]),
                                _ => p,
                            },
                            _ => app("OOpt", vec![p]),
                        };
                        fields.push((format!("f{f}"), ty));
                    }
                    let result = if indexed[m] {
                        vec![T::Lit(rng.below(2) as u32)]
                    } else {
                        vec![]
                    };
                    Ctor {
                        name: format!("R{k}m{m}c{c}"),
                        fields,
                        result,
                    }
                })
                .collect();
            Member {
                name: names[m].clone(),
                indices: if indexed[m] {
                    vec![name("Nat")]
                } else {
                    vec![]
                },
                ctors,
            }
        })
        .collect();
    Group {
        params,
        prop: false,
        members,
    }
}

/// What a field's type is generated in: the group under test, its
/// containers, and the constructor's earlier fields.
struct Gen<'a> {
    containers: &'a [&'a Group],
    params: Vec<String>,
    members: Vec<(String, bool)>,
    prop: bool,
    earlier: Vec<(String, T)>,
    fresh: usize,
}

impl Gen<'_> {
    fn member_ref(&mut self, rng: &mut Rng, index: Option<T>) -> T {
        let (m, indexed) = rng.pick(&self.members).clone();
        let mut args: Vec<T> = self.params.iter().map(|x| name(x)).collect();
        if indexed {
            args.push(index.unwrap_or_else(|| self.number(rng)));
        }
        app(&m, args)
    }

    /// A number: a literal or an earlier `Nat` field.
    fn number(&mut self, rng: &mut Rng) -> T {
        let nats: Vec<String> = self
            .earlier
            .iter()
            .filter(|(_, t)| *t == name("Nat"))
            .map(|(x, _)| x.clone())
            .collect();
        if !nats.is_empty() && rng.chance(50) {
            name(rng.pick(&nats))
        } else {
            T::Lit(rng.below(2) as u32)
        }
    }

    /// A field's type, or with `arg`, a container's `Type` argument (which
    /// must be a type in `Type`: not an equation, nor a member of a `Prop`
    /// group).
    fn ty(&mut self, rng: &mut Rng, depth: usize, arg: bool) -> T {
        let choice = if depth >= 2 {
            rng.below(3)
        } else {
            rng.below(12)
        };
        let members_are_types = !self.prop;
        match choice {
            0 => name("Nat"),
            1 if !self.params.is_empty() => name(&self.params[0].clone()),
            3..=7 => self.container(rng, depth, arg),
            8 => {
                let dom = match rng.below(4) {
                    1 if !members_are_types => self.member_ref(rng, None),
                    0 | 1 => name("Nat"),
                    2 if members_are_types => app("OList", vec![self.member_ref(rng, None)]),
                    _ if members_are_types => app("OOpt", vec![self.member_ref(rng, None)]),
                    _ => self.member_ref(rng, None),
                };
                arrow(dom, self.ty(rng, depth + 1, arg))
            }
            9 if !arg => {
                // An equation between two earlier fields of the same type.
                let pairs: Vec<(String, String)> = self
                    .earlier
                    .iter()
                    .enumerate()
                    .flat_map(|(i, (x, t))| {
                        self.earlier[i..]
                            .iter()
                            .filter(move |(_, u)| u == t)
                            .map(move |(y, _)| (x.clone(), y.clone()))
                    })
                    .collect();
                match pairs.is_empty() {
                    true => name("Nat"),
                    false => {
                        let (x, y) = rng.pick(&pairs).clone();
                        equal(name(&x), name(&y))
                    }
                }
            }
            _ if arg && !members_are_types => name("Nat"),
            _ => self.member_ref(rng, None),
        }
    }

    /// A container applied to generated arguments; with `arg`, one in
    /// `Type`.
    fn container(&mut self, rng: &mut Rng, depth: usize, arg: bool) -> T {
        let g = loop {
            let g = *rng.pick(self.containers);
            if !(arg && g.prop) {
                break g;
            }
        };
        let m = rng.pick(&g.members).clone();
        let mut args: Vec<T> = Vec::new();
        let mut instance: BTreeMap<String, T> = BTreeMap::new();
        for (x, pty) in &g.params {
            let arg = match pty {
                t if *t == name("Type") => self.ty(rng, depth + 1, true),
                T::Arrow(dom, _) => {
                    let t = format!("t{}", self.fresh);
                    self.fresh += 1;
                    let dom = dom.subst(&instance);
                    let body = match rng.below(3) {
                        0 if self.prop && dom == name("Nat") => {
                            self.member_ref(rng, Some(name(&t)))
                        }
                        1 if self.prop => self.member_ref(rng, None),
                        _ => equal(name(&t), name(&t)),
                    };
                    lam(&t, body)
                }
                // `ODep`'s list.
                _ => name("ONil"),
            };
            instance.insert(x.clone(), arg.clone());
            args.push(arg);
        }
        for index in &m.indices {
            let index = index.subst(&instance);
            args.push(if index == name("Nat") {
                self.number(rng)
            } else if let T::App(l, _) = &index
                && l == "OList"
            {
                name("ONil")
            } else {
                // `OIdx`'s index, of the instance's type: an earlier field
                // of that type, or if there's none, an `OOpt` instead.
                let same: Vec<String> = self
                    .earlier
                    .iter()
                    .filter(|(_, t)| *t == index)
                    .map(|(x, _)| x.clone())
                    .collect();
                match same.is_empty() {
                    true => return app("OOpt", vec![args[0].clone()]),
                    false => name(rng.pick(&same)),
                }
            });
        }
        app(&m.name, args)
    }
}

/// The group under test: `N0` and maybe `N1`, maybe a `Type` parameter `s`,
/// each maybe indexed by a number, 1-3 constructors of 0-3 fields.
fn random_group(rng: &mut Rng, containers: &[&Group]) -> Group {
    let params: Vec<String> = if rng.chance(40) {
        vec!["s".to_string()]
    } else {
        vec![]
    };
    let prop = rng.chance(20);
    let count = 1 + usize::from(rng.chance(30));
    let members: Vec<(String, bool)> = (0..count)
        .map(|m| (format!("N{m}"), rng.chance(30)))
        .collect();
    let mut fields_gen = Gen {
        containers,
        params: params.clone(),
        members: members.clone(),
        prop,
        earlier: Vec::new(),
        fresh: 0,
    };
    let members = members
        .iter()
        .enumerate()
        .map(|(m, (mname, indexed))| {
            let ctors = (0..1 + rng.below(3))
                .map(|c| {
                    fields_gen.earlier.clear();
                    for f in 0..rng.below(4) {
                        let ty = fields_gen.ty(rng, 0, false);
                        fields_gen.earlier.push((format!("g{f}"), ty));
                    }
                    let result = match indexed {
                        true => {
                            let n = fields_gen.number(rng);
                            vec![if rng.chance(50) {
                                app("Succ", vec![n])
                            } else {
                                n
                            }]
                        }
                        false => vec![],
                    };
                    Ctor {
                        name: format!("N{m}c{c}"),
                        fields: std::mem::take(&mut fields_gen.earlier),
                        result,
                    }
                })
                .collect();
            Member {
                name: mname.clone(),
                indices: if *indexed { vec![name("Nat")] } else { vec![] },
                ctors,
            }
        })
        .collect();
    Group {
        params: params.into_iter().map(|x| (x, name("Type"))).collect(),
        prop,
        members,
    }
}

// --- the seeds ---------------------------------------------------------

/// The groups under test written by hand: the examples in
/// `examples/accept/nested-data*.sw` and `examples/soundness/nested-*.sw`,
/// over this file's containers.
fn seeds() -> Vec<(&'static str, Group)> {
    let nat = || name("Nat");
    let n0 = || name("N0");
    let one = |fields: Vec<(&str, T)>| {
        group(
            vec![],
            false,
            vec![member(
                "N0",
                vec![],
                vec![ctor("N0c0", vec![], vec![]), ctor("N0c1", fields, vec![])],
            )],
        )
    };
    vec![
        ("Packet", one(vec![("g0", app("OList", vec![n0()]))])),
        (
            "Rose",
            group(
                vec![("s", name("Type"))],
                false,
                vec![member(
                    "N0",
                    vec![],
                    vec![ctor(
                        "N0c0",
                        vec![
                            ("g0", name("s")),
                            ("g1", app("OList", vec![app("N0", vec![name("s")])])),
                        ],
                        vec![],
                    )],
                )],
            ),
        ),
        (
            "List (List T)",
            one(vec![("g0", app("OList", vec![app("OList", vec![n0()])]))]),
        ),
        (
            "Option (T, Nat)",
            one(vec![(
                "g0",
                app("OOpt", vec![app("OPair", vec![n0(), nat()])]),
            )]),
        ),
        (
            "Vec T 2",
            one(vec![("g0", app("OVec", vec![n0(), T::Lit(2)]))]),
        ),
        (
            "in a mutual container",
            one(vec![("g0", app("OTree", vec![n0()]))]),
        ),
        ("Phantom", one(vec![("g0", app("OPhantom", vec![n0()]))])),
        (
            "W at its stored parameter",
            one(vec![("g0", app("OW", vec![n0(), nat()]))]),
        ),
        (
            "W at its input",
            one(vec![("g0", app("OW", vec![nat(), n0()]))]),
        ),
        ("Neg", one(vec![("g0", app("ONeg", vec![n0()]))])),
        (
            "Option as input",
            one(vec![("g0", arrow(app("OOpt", vec![n0()]), nat()))]),
        ),
        (
            "Dep (§5.5)",
            one(vec![("g0", app("ODep", vec![n0(), name("ONil")]))]),
        ),
        (
            "Idx",
            one(vec![(
                "g0",
                app("OIdx", vec![app("OList", vec![n0()]), name("ONil")]),
            )]),
        ),
        (
            "Fnat",
            one(vec![
                ("g0", n0()),
                ("g1", n0()),
                ("g2", equal(name("g0"), name("g1"))),
            ]),
        ),
        (
            "lenOk-like",
            one(vec![
                ("g0", app("OList", vec![n0()])),
                ("g1", equal(name("g0"), name("g0"))),
            ]),
        ),
        (
            "Eq on non-recursive fields",
            one(vec![
                ("g0", nat()),
                ("g1", nat()),
                ("g2", equal(name("g0"), name("g1"))),
                ("g3", app("OList", vec![n0()])),
            ]),
        ),
        (
            "List (Tree n)",
            group(
                vec![],
                false,
                vec![member(
                    "N0",
                    vec![nat()],
                    vec![
                        ctor("N0c0", vec![], vec![T::Lit(0)]),
                        ctor(
                            "N0c1",
                            vec![
                                ("g0", nat()),
                                ("g1", app("OList", vec![app("N0", vec![name("g0")])])),
                            ],
                            vec![app("Succ", vec![name("g0")])],
                        ),
                    ],
                )],
            ),
        ),
        (
            "All (t => Typed t r) bs",
            group(
                vec![],
                true,
                vec![member(
                    "N0",
                    vec![nat(), nat()],
                    vec![
                        ctor("N0c0", vec![("g0", nat())], vec![T::Lit(0), name("g0")]),
                        ctor(
                            "N0c1",
                            vec![
                                ("g0", nat()),
                                ("g1", app("OList", vec![nat()])),
                                (
                                    "g2",
                                    app(
                                        "OAll",
                                        vec![
                                            nat(),
                                            lam("t0", app("N0", vec![name("t0"), name("g0")])),
                                            name("g1"),
                                        ],
                                    ),
                                ),
                            ],
                            vec![T::Lit(1), name("g0")],
                        ),
                    ],
                )],
            ),
        ),
        (
            "two members, both nested",
            group(
                vec![],
                false,
                vec![
                    member(
                        "N0",
                        vec![],
                        vec![ctor(
                            "N0c0",
                            vec![("g0", app("OList", vec![name("N1")]))],
                            vec![],
                        )],
                    ),
                    member(
                        "N1",
                        vec![],
                        vec![
                            ctor("N1c0", vec![("g0", nat())], vec![]),
                            ctor("N1c1", vec![("g0", app("OOpt", vec![n0()]))], vec![]),
                        ],
                    ),
                ],
            ),
        ),
    ]
}

// --- running -------------------------------------------------------------

/// Each case's session gets this much stack, on a pool of its own.
const STACK: usize = 64 * 1024 * 1024;

/// The first error's code and message, if the program is refused.
fn check(text: &str) -> Result<(), (&'static str, String)> {
    let mut session = Session::for_stack(STACK);
    session
        .load("oracle.sw", text)
        .map(|_| ())
        .map_err(|ds| (ds[0].code, ds[0].message.clone()))
}

/// One case: the earlier groups it adds to the library, and the group
/// under test.
struct Case {
    label: String,
    earlier: Vec<Group>,
    group: Group,
}

/// What a case gave.
enum Outcome {
    /// The nested program was accepted, and so was its translation.
    Agree,
    /// Refused by positivity; with the translated program, if there is one
    /// and it's accepted (property 2's counterexample).
    Refused(Option<String>),
    /// Refused because of something else (the generator wrote something
    /// ill-typed).
    Other(&'static str, String),
    /// Property 1 failed: the report.
    Disagree(String),
}

fn run_case(case: &Case) -> Outcome {
    let lib = library();
    let mut env_groups: Vec<&Group> = lib.iter().collect();
    env_groups.extend(case.earlier.iter());
    let mut all = env_groups.clone();
    all.push(&case.group);
    let nested = program(&all);
    let verdict = check(&nested);
    // The elaborator groups the members that refer to each other: each
    // group is translated with the ones before it as containers.
    let parts = components(&case.group);
    let mut translation: Result<Vec<Group>, String> = Ok(Vec::new());
    for (k, part) in parts.iter().enumerate() {
        let mut groups = env_groups.clone();
        groups.extend(&parts[..k]);
        let env = Env { groups };
        translation = translation.and_then(|mut done| {
            done.push(translate(&env, part, k)?);
            Ok(done)
        });
    }
    let translated = translation.as_ref().ok().map(|parts| {
        let mut all = env_groups.clone();
        all.extend(parts.iter());
        program(&all)
    });
    let label = &case.label;
    match (verdict, translated) {
        (Ok(()), None) => Outcome::Disagree(format!(
            "property 1 ({label}): the nested group is accepted, but has no translation \
             ({})\n\n{nested}",
            translation.err().unwrap_or_default()
        )),
        (Ok(()), Some(text)) => match check(&text) {
            Ok(()) => Outcome::Agree,
            Err((code, message)) => Outcome::Disagree(format!(
                "property 1 ({label}): the nested group is accepted, but its translation isn't: \
                 [{code}] {message}\n\n--- nested ---\n{nested}\n--- translated ---\n{text}"
            )),
        },
        (Err(("E-POSITIVITY", message)), Some(text)) if check(&text).is_ok() => {
            Outcome::Refused(Some(format!(
                "{label}: {message}\n--- nested ---\n{nested}\n--- translated ---\n{text}"
            )))
        }
        (Err(("E-POSITIVITY", _)), _) => Outcome::Refused(None),
        (Err((code, message)), _) => Outcome::Other(code, format!("{message}\n{nested}")),
    }
}

/// Runs the cases on a pool; panics with the first property 1 failure.
/// Each outcome, in order.
fn run_all(cases: &[Case]) -> Vec<Outcome> {
    let outcomes = with_stack(STACK, || par_map(STACK, cases, run_case));
    if let Some(Outcome::Disagree(report)) =
        outcomes.iter().find(|o| matches!(o, Outcome::Disagree(_)))
    {
        panic!("{report}");
    }
    outcomes
}

#[test]
fn the_library_of_containers_checks() {
    let lib = library();
    let all: Vec<&Group> = lib.iter().collect();
    let text = program(&all);
    let result = with_stack(STACK, || check(&text));
    if let Err((code, message)) = result {
        panic!("[{code}] {message}\n\n{text}");
    }
}

#[test]
fn the_seeds_get_their_verdicts() {
    // Accepted (and so, by property 1, their translations are), or refused
    // by positivity.
    let accepted = [
        "Packet",
        "Rose",
        "List (List T)",
        "Option (T, Nat)",
        "Vec T 2",
        "in a mutual container",
        "Phantom",
        "W at its stored parameter",
        "Eq on non-recursive fields",
        "List (Tree n)",
        "All (t => Typed t r) bs",
        "two members, both nested",
    ];
    let cases: Vec<Case> = seeds()
        .into_iter()
        .map(|(label, group)| Case {
            label: label.to_string(),
            earlier: Vec::new(),
            group,
        })
        .collect();
    let outcomes = run_all(&cases);
    let mut incomplete = Vec::new();
    for (case, outcome) in cases.iter().zip(&outcomes) {
        let label = case.label.as_str();
        match outcome {
            Outcome::Agree => assert!(accepted.contains(&label), "{label} is accepted"),
            Outcome::Refused(translated) => {
                assert!(!accepted.contains(&label), "{label} is refused");
                if translated.is_some() {
                    incomplete.push(label);
                }
            }
            Outcome::Other(code, message) => panic!("{label}: [{code}] {message}"),
            Outcome::Disagree(_) => unreachable!(),
        }
    }
    // §5.5's restriction is the one incompleteness among the seeds.
    assert_eq!(incomplete, ["Dep (§5.5)"]);
}

#[test]
fn nested_accepted_means_translation_accepted() {
    let count = std::env::var("ORACLE_CASES")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(match tier() {
            Tier::Lane | Tier::Merge => 50,
            Tier::Daily => 400,
            Tier::Full => 4000,
        });
    let seed = std::env::var("ORACLE_SEED")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(0x5eed_0704_u64);
    let mut rng = Rng(seed);
    let lib = library();
    let mut cases: Vec<Case> = seeds()
        .into_iter()
        .take(count)
        .map(|(label, group)| Case {
            label: label.to_string(),
            earlier: Vec::new(),
            group,
        })
        .collect();
    for case in cases.len()..count {
        let earlier: Vec<Group> = (0..rng.below(3))
            .map(|k| random_outer(&mut rng, k))
            .collect();
        let mut containers: Vec<&Group> = lib.iter().collect();
        containers.extend(earlier.iter());
        let group = random_group(&mut rng, &containers);
        cases.push(Case {
            label: format!("case {case} (seed {seed})"),
            earlier,
            group,
        });
    }
    let outcomes = run_all(&cases);
    let agree = outcomes
        .iter()
        .filter(|o| matches!(o, Outcome::Agree))
        .count();
    let refused = outcomes
        .iter()
        .filter(|o| matches!(o, Outcome::Refused(_)))
        .count();
    let incomplete: Vec<&String> = outcomes
        .iter()
        .filter_map(|o| match o {
            Outcome::Refused(Some(report)) => Some(report),
            _ => None,
        })
        .collect();
    // The other refusals, by code, each with its first message.
    let mut other: std::collections::BTreeMap<&str, (usize, &String)> = Default::default();
    for o in &outcomes {
        if let Outcome::Other(code, message) = o {
            other.entry(code).or_insert((0, message)).0 += 1;
        }
    }
    eprintln!(
        "{} cases: {agree} nested accepted, each translation accepted; {refused} refused by \
         positivity, {} of them with an accepted translation (property 2, reported); {} refused \
         otherwise",
        cases.len(),
        incomplete.len(),
        other.values().map(|(n, _)| n).sum::<usize>(),
    );
    for (code, (n, message)) in &other {
        eprintln!("  {n} × [{code}], first: {message}");
    }
    // Property 2's counterexamples, by kind: §5.5's restriction (a
    // parameter a later parameter's type mentions), and the rest, the first
    // few of which are printed.
    let (restriction, rest): (Vec<&String>, Vec<&String>) = incomplete
        .iter()
        .partition(|report| report.contains("later parameter"));
    eprintln!(
        "property 2: {} from §5.5's restriction, {} otherwise",
        restriction.len(),
        rest.len()
    );
    let show = std::env::var("ORACLE_SHOW")
        .ok()
        .and_then(|n| n.parse().ok())
        .unwrap_or(3);
    for report in rest.iter().take(show) {
        eprintln!("property 2 (reported, not required):\n{report}\n");
    }
}

//! Named arguments are sugar (docs/proposals/named-arguments.md §7,
//! acceptance invariants 1 and 5): naming a call's arguments, without
//! changing the written order or the bracketing, gives the same elaborated
//! term, so every declaration keeps its content hash.
//!
//! `named_calls_keep_every_hash` is the differential test: every
//! `examples/accept` file that loads in a fresh session is loaded again with
//! the explicit arguments of its calls of definitions written by name,
//! `f a b` becoming `f (x := a) (y := b)`, and every declaration must have
//! the same hash. A call is rewritten when its head is a definition found by
//! its full name (the file's own, or the library's as `List.map`), not a
//! name the file binds anywhere else, and only the arguments whose
//! parameters have names (in the definition's declared type). Effectful
//! calls are rewritten too: the effect trace is the term's.
//!
//! `named_forms_have_the_positional_hash` checks pairs written both ways in
//! one file: method sections, dot notation, pipes and constructors.
//!
//! `NAMED_ARGUMENTS=<text>` limits the differential test to the files whose
//! name contains it.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path;

use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::{DataId, DefId, Icit, Term};
use stitchwort_driver::driver::{Session, par_map_with};
use stitchwort_driver::rewind::Mark;
use stitchwort_syntax::ast::{Clause, Decl, Expr, Pattern};
use stitchwort_syntax::{SourceMap, Span, parse_module};

const STACK: usize = 16 * 1024 * 1024;

fn show(h: stitchwort_core::budget::Result<Option<ContentHash>>) -> String {
    match h {
        Ok(Some(h)) => h.hex(),
        _ => "<none>".to_string(),
    }
}

/// Every declaration the session added after `first`, with its hash.
fn hashes(session: &Session, first: (usize, usize)) -> Vec<(String, String)> {
    let g = &session.elab.globals;
    let mut out = Vec::new();
    for i in first.0..g.datas.len() {
        out.push((
            format!("data {}", g.datas[i].path),
            show(data_hash(g, DataId(i))),
        ));
    }
    for i in first.1..g.defs.len() {
        out.push((g.defs[i].path.to_string(), show(def_hash(g, DefId(i)))));
    }
    out
}

/// Loads `text` in a fresh session: its declarations' hashes, or the
/// errors.
fn load(name: &str, text: &str) -> Result<(Session, Vec<(String, String)>), String> {
    let mut session = Session::eager_for_stack(STACK);
    let found = load_in(&mut session, name, text)?;
    Ok((session, found))
}

/// Loads `text` in `session`: the hashes of the declarations it adds, or
/// the errors.
fn load_in(session: &mut Session, name: &str, text: &str) -> Result<Vec<(String, String)>, String> {
    let first = (
        session.elab.globals.datas.len(),
        session.elab.globals.defs.len(),
    );
    match session.load(name, text) {
        Ok(_) => Ok(hashes(session, first)),
        Err(errors) => Err(errors
            .iter()
            .map(|e| format!("{}: {}", e.code, e.message))
            .collect::<Vec<_>>()
            .join("\n")),
    }
}

/// A worker's eager session (the whole library loaded, a second or two),
/// marked: rewound to the mark before each load, it is a fresh eager
/// session without loading the library again (the rewind tests check that
/// rewinding gives exactly what a fresh session does).
fn eager_worker() -> (Session, Mark) {
    let session = Session::eager_for_stack(STACK);
    let mark = session.mark();
    (session, mark)
}

/// The names a file binds anywhere (parameters, lambdas, `let`s, pattern
/// variables, handler clauses, local definitions): a call headed by one of
/// these may not be of the definition of that name.
#[derive(Default)]
struct Walk {
    bound: BTreeSet<String>,
    /// Calls: the head's name, whether a pipe passes the first explicit
    /// argument (`x |> f a`, rule E), and the spans of its arguments
    /// (`None` for one already named).
    calls: Vec<(String, bool, Vec<Option<Span>>)>,
    /// The span of the right side of the pipe being walked.
    piped: Option<Span>,
}

impl Walk {
    fn pattern(&mut self, p: &Pattern) {
        match p {
            Pattern::Var(n) => {
                self.bound.insert(n.text.clone());
            }
            Pattern::Ctor(_, ps, _) => ps.iter().for_each(|p| self.pattern(p)),
            Pattern::Tuple(a, b, _) | Pattern::Cons(a, b, _) => {
                self.pattern(a);
                self.pattern(b);
            }
            Pattern::Named(_, p, _) => self.pattern(p),
            Pattern::Or(alternatives, _) => alternatives.iter().for_each(|p| self.pattern(p)),
            Pattern::Record { fields, .. } | Pattern::CtorFields { fields, .. } => {
                for (name, p) in fields {
                    self.bound.insert(name.text.clone());
                    self.pattern(p);
                }
            }
            _ => {}
        }
    }

    fn decl(&mut self, d: &Decl) {
        match d {
            Decl::Signature { ty, decreasing, .. } => {
                self.expr(ty);
                if let Some(e) = decreasing {
                    self.expr(e);
                }
            }
            Decl::Equation { patterns, rhs, .. } => {
                patterns.iter().for_each(|p| self.pattern(p));
                if let Some(rhs) = rhs {
                    self.expr(rhs);
                }
            }
            Decl::Test { expr, .. } => self.expr(expr),
            Decl::Data { params, ctors, .. } => {
                for b in params {
                    b.names.iter().for_each(|n| {
                        self.bound.insert(n.text.clone());
                    });
                }
                for c in ctors {
                    for b in &c.fields {
                        b.names.iter().for_each(|n| {
                            self.bound.insert(n.text.clone());
                        });
                    }
                    c.defaults.iter().flatten().for_each(|e| self.expr(e));
                }
            }
            Decl::Ability { ops, .. } => {
                for (name, _) in ops {
                    self.bound.insert(name.text.clone());
                }
            }
        }
    }

    fn expr(&mut self, e: &Expr) {
        match e {
            Expr::App(..) => {
                let mut args = Vec::new();
                let mut head = e;
                while let Expr::App(f, a) = head {
                    args.push(a.as_ref());
                    head = f;
                }
                args.reverse();
                if let Expr::Var(name) = head {
                    let spans = (args.iter())
                        .map(|a| match a {
                            Expr::NamedArg(..) => None,
                            other => Some(other.span()),
                        })
                        .collect();
                    let piped = self.piped == Some(e.span());
                    self.calls.push((name.text.clone(), piped, spans));
                } else {
                    self.expr(head);
                }
                args.iter().for_each(|a| self.expr(a));
            }
            Expr::Lam(names, body, _) => {
                names.iter().for_each(|n| {
                    self.bound.insert(n.text.clone());
                });
                self.expr(body);
            }
            Expr::TypedLam(name, _, ty, body, _) => {
                self.bound.insert(name.text.clone());
                self.expr(ty);
                self.expr(body);
            }
            Expr::Pi {
                names, dom, cod, ..
            } => {
                names.iter().for_each(|n| {
                    self.bound.insert(n.text.clone());
                });
                self.expr(dom);
                self.expr(cod);
            }
            Expr::NamedArg(_, value, ..)
            | Expr::Neg(value, _, _)
            | Expr::Interpolated(value, _)
            | Expr::Field(value, _) => self.expr(value),
            Expr::Pipe(a, b) => {
                self.expr(a);
                self.piped = Some(b.span());
                self.expr(b);
            }
            Expr::Arrow(a, b)
            | Expr::Binary(_, a, b)
            | Expr::Seq(a, b)
            | Expr::Ann(a, b, _)
            | Expr::Tuple(a, b, _) => {
                self.expr(a);
                self.expr(b);
            }
            Expr::If {
                binder,
                cond,
                then,
                otherwise,
                ..
            } => {
                if let Some(b) = binder {
                    self.bound.insert(b.text.clone());
                }
                self.expr(cond);
                self.expr(then);
                self.expr(otherwise);
            }
            Expr::Let {
                name,
                ty,
                value,
                body,
                ..
            } => {
                self.bound.insert(name.text.clone());
                if let Some(ty) = ty {
                    self.expr(ty);
                }
                self.expr(value);
                self.expr(body);
            }
            Expr::LocalDefs { defs, body, .. } => {
                for def in defs {
                    if let Decl::Signature { name, .. } = &def.signature {
                        self.bound.insert(name.text.clone());
                    }
                    self.decl(&def.signature);
                    def.equations.iter().for_each(|d| self.decl(d));
                }
                self.expr(body);
            }
            Expr::Handle { body, clauses, .. }
            | Expr::Reify {
                thunk: body,
                clauses,
                ..
            } => {
                self.expr(body);
                for clause in clauses {
                    match clause {
                        Clause::Return { var, body } => {
                            self.bound.insert(var.text.clone());
                            self.expr(body);
                        }
                        Clause::Op { arg, k, body, .. } => {
                            self.pattern(arg);
                            self.bound.insert(k.text.clone());
                            self.expr(body);
                        }
                    }
                }
            }
            Expr::Match {
                scrutinees, alts, ..
            } => {
                for s in scrutinees {
                    if let Some(n) = &s.name {
                        self.bound.insert(n.text.clone());
                    }
                    self.expr(&s.expr);
                }
                for alt in alts {
                    alt.patterns.iter().for_each(|p| self.pattern(p));
                    self.expr(&alt.body);
                }
            }
            Expr::List(items, _) => items.iter().for_each(|i| self.expr(i)),
            Expr::Record { base, fields, .. } => {
                if let Some(b) = base {
                    self.expr(b);
                }
                fields.iter().for_each(|(_, e)| self.expr(e));
            }
            Expr::CtorFields { fields, .. } => fields.iter().for_each(|(_, e)| self.expr(e)),
            // Anything else is left as written.
            _ => {}
        }
    }
}

/// The names of the leading parameters of a definition's declared type,
/// with their kinds: `None` for one that can't be named (`_`, a generated
/// name, or a name the type repeats).
fn parameters(ty: &Term) -> Vec<(Icit, Option<String>)> {
    let mut out = Vec::new();
    let mut ty = ty.strip_loc();
    while let Term::Pi(x, icit, _, cod) = ty {
        let name = x.to_string();
        let usable = !name.is_empty() && name != "_" && !name.starts_with('%');
        out.push((*icit, usable.then_some(name)));
        ty = cod.strip_loc();
    }
    let mut seen: BTreeMap<String, usize> = BTreeMap::new();
    for (_, name) in &out {
        if let Some(n) = name {
            *seen.entry(n.clone()).or_default() += 1;
        }
    }
    for (_, name) in &mut out {
        if name.as_ref().is_some_and(|n| seen[n] > 1) {
            *name = None;
        }
    }
    out
}

/// `text` with the explicit arguments of the calls in `walk` named, as far
/// as `session` (the file loaded as written) knows their parameters' names;
/// and how many arguments were named.
fn named(session: &Session, text: &str, walk: &Walk) -> (String, usize) {
    let g = &session.elab.globals;
    let by_path: BTreeMap<String, usize> = (0..g.defs.len())
        .map(|i| (g.defs[i].path.to_string(), i))
        .collect();
    // Insertions, as (offset, order, text): an argument's opening comes
    // after the closings of those that end where it starts, and before
    // the openings of those it contains.
    let mut inserts: Vec<(u32, i64, String)> = Vec::new();
    let mut count = 0;
    for (head, piped, args) in &walk.calls {
        if walk.bound.contains(head) {
            continue;
        }
        let Some(&id) = by_path
            .get(&format!("Main.{head}"))
            .or_else(|| by_path.get(&format!("Std.{head}")))
        else {
            continue;
        };
        let params = parameters(&g.defs[id].ty);
        // Positional arguments skip the parameters with defaults.
        let defaults = g.defs[id].param_defaults.as_deref();
        let defaulted =
            |k: usize| defaults.is_some_and(|d| d.params.get(k).is_some_and(Option::is_some));
        let mut explicit = params
            .iter()
            .enumerate()
            .filter(|(k, (icit, _))| *icit == Icit::Explicit && !defaulted(*k))
            .map(|(_, param)| param);
        if *piped {
            // The pipe's value is the first explicit argument (rule E).
            explicit.next();
        }
        for arg in args {
            let Some(span) = arg else {
                // Already named: the rest of the call is left alone.
                break;
            };
            let Some((_, name)) = explicit.next() else {
                break;
            };
            let Some(name) = name else {
                continue;
            };
            // An argument already in brackets is named inside them, so a
            // block in it (`f (\n  let …`) keeps its layout.
            let bytes = text.as_bytes();
            let before = bytes[..span.start as usize]
                .iter()
                .rposition(|b| !b.is_ascii_whitespace());
            let after = bytes[span.end as usize..]
                .iter()
                .position(|b| !b.is_ascii_whitespace());
            match (before, after) {
                (Some(open), Some(close))
                    if bytes[open] == b'(' && bytes[span.end as usize + close] == b')' =>
                {
                    inserts.push((open as u32 + 1, i64::MAX, format!("{name} := ")));
                }
                _ => {
                    let width = i64::from(span.end - span.start);
                    inserts.push((span.start, width, format!("({name} := ")));
                    inserts.push((span.end, -width, ")".to_string()));
                }
            }
            count += 1;
        }
    }
    // Applied from the end, so earlier offsets stay right. At one offset:
    // closings (negative order) first, then openings of the widest argument
    // first, so the narrower one ends up inside it.
    inserts.sort_by(|a, b| b.0.cmp(&a.0).then(a.1.cmp(&b.1)));
    let mut out = text.to_string();
    for (offset, _, piece) in inserts {
        out.insert_str(offset as usize, &piece);
    }
    (out, count)
}

#[test]
fn named_calls_keep_every_hash() {
    let filter = std::env::var("NAMED_ARGUMENTS").unwrap_or_default();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/accept");
    let mut files: Vec<_> = std::fs::read_dir(&root)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "sw"))
        .filter(|p| p.file_name().unwrap().to_string_lossy().contains(&filter))
        .collect();
    files.sort();
    let results = par_map_with(STACK, &files, eager_worker, |(session, mark), path| {
        let name = path.display().to_string();
        let text = std::fs::read_to_string(path).unwrap();
        session.rewind(mark);
        let Ok(before) = load_in(session, &name, &text) else {
            return (0, 0, Vec::new());
        };
        let mut sources = SourceMap::new();
        let file = sources.add(name.clone(), text.clone());
        let Ok(module) = parse_module(file, &text) else {
            return (0, 0, Vec::new());
        };
        let mut walk = Walk::default();
        module.decls.iter().for_each(|d| walk.decl(d));
        let (rewritten, count) = named(session, &text, &walk);
        if count == 0 {
            return (1, 0, Vec::new());
        }
        let mut failures = Vec::new();
        session.rewind(mark);
        match load_in(session, &name, &rewritten) {
            Err(errors) => failures.push(format!(
                "{name}: doesn't load with named arguments:\n{errors}\n--- rewritten:\n{rewritten}"
            )),
            Ok(after) if after != before => {
                for ((n1, h1), (n2, h2)) in before.iter().zip(&after) {
                    if n1 != n2 || h1 != h2 {
                        failures.push(format!("{name}: {n1} {h1} became {n2} {h2}"));
                    }
                }
                if before.len() != after.len() {
                    failures.push(format!("{name}: a different number of declarations"));
                }
            }
            Ok(_) => {}
        }
        (1, count, failures)
    });
    let files_checked: usize = results.iter().map(|r| r.0).sum();
    let named_args: usize = results.iter().map(|r| r.1).sum();
    let failures: Vec<&String> = results.iter().flat_map(|r| &r.2).collect();
    eprintln!("{files_checked} files, {named_args} arguments named");
    assert!(
        failures.is_empty(),
        "{} failure(s):\n{}",
        failures.len(),
        failures
            .iter()
            .map(|s| s.as_str())
            .collect::<Vec<_>>()
            .join("\n\n")
    );
    if filter.is_empty() {
        assert!(named_args > 1000, "only {named_args} arguments were named");
    }
}

/// Each `positional`/`named` pair of definitions must have one hash.
#[test]
fn named_forms_have_the_positional_hash() {
    let text = r#"
type Point = { x: Nat, y: Nat }

def Point.shift (point: Point) (dx: Nat) (dy: Nat): Point :=
  { x = point.x + dx, y = point.y + dy }

def Point.scale (point: Point) (by: Nat) (plus: Nat): Point :=
  { x = point.x * by + plus, y = point.y * by + plus }

def clampTo (value: Nat) (low: Nat) (high: Nat): Nat :=
  if value < low then low else if value > high then high else value

def pick [count: Nat] [label: Text] (x: Nat): Nat := x + count

type Shape =
  | Circle (radius: Nat) (id: Text)
  | Square (side: Nat)

def corner: Point := { x = 1, y = 5 }

def sectionPositional (points: List Point): List Point := points.map (.shift 2 1)
def sectionNamed (points: List Point): List Point := points.map (.shift (dy := 1) (dx := 2))

def splitPositional (lines: List Text): List (List Text) := lines.map (.split ',')
def splitNamed (lines: List Text): List (List Text) := lines.map (.split (separator := ','))

def dotPositional: Point := corner.scale 2 1
def dotNamed: Point := corner.scale (plus := 1) (by := 2)

def pipePositional: Nat := 5 |> clampTo 0 3
def pipeNamed: Nat := 5 |> clampTo (high := 3) (low := 0)

def callPositional: Nat := clampTo 5 0 3
def callNamed: Nat := clampTo (value := 5) (high := 3) (low := 0)

def implicitPositional: Nat := pick [count := 3] [label := "a"] 1
def implicitNamed: Nat := pick [label := "a"] (x := 1) [count := 3]

def ctorPositional: Shape := Circle 1 "a"
def ctorNamed: Shape := Circle (id := "a") (radius := 1)

def mixedPositional: Nat := clampTo 1 3 2
def mixedNamed: Nat := clampTo (high := 2) 1 3
"#;
    let (_, found) = load("named-forms.sw", text).expect("the file loads");
    let by_name: BTreeMap<&str, &str> = found
        .iter()
        .map(|(n, h)| (n.as_str(), h.as_str()))
        .collect();
    let mut checked = 0;
    for (name, hash) in &by_name {
        let Some(stem) = name.strip_suffix("Positional") else {
            continue;
        };
        let named = format!("{stem}Named");
        assert_eq!(
            Some(hash),
            by_name.get(named.as_str()),
            "{name} and {named} differ"
        );
        checked += 1;
    }
    assert_eq!(checked, 8);
}

/// The hash of each declaration `text` adds, by full name (`data …` for a
/// data type).
fn hashes_by_name(text: &str) -> BTreeMap<String, String> {
    let (_, found) = load("field-defaults.sw", text).expect("the file loads");
    found.into_iter().collect()
}

const DEFAULTS: &str = r#"
type RangeOptions = {
  start: Nat := START,
  stop: Nat,
  step: Nat := 1
}

type Shape =
  | Circle (radius: Nat) (id: Text := "anonymous")

def leavesStartOut: RangeOptions := { stop = 10 }
def givesStart: RangeOptions := { start = 2, stop = 10 }
def givesEvery: RangeOptions := { start = 2, stop = 10, step = 3 }
def leavesIdOut: Shape := Circle { radius = 1 }
"#;

/// Field defaults (docs/proposals/named-arguments.md §7, acceptance
/// invariant 9): changing a default changes the hashes of exactly the
/// literals that leave that field out, and its helper's; the type and the
/// literals that give the field keep theirs.
#[test]
fn changing_a_default_changes_only_the_literals_that_use_it() {
    let before = hashes_by_name(&DEFAULTS.replace("START", "0"));
    let after = hashes_by_name(&DEFAULTS.replace("START", "5"));
    let changed: BTreeSet<&str> = before
        .iter()
        .filter(|(name, hash)| after.get(*name) != Some(hash))
        .map(|(name, _)| name.as_str())
        .collect();
    assert_eq!(
        changed,
        BTreeSet::from(["Main.RangeOptions.start%default", "Main.leavesStartOut"]),
        "before: {before:#?}\nafter: {after:#?}"
    );
    assert!(before.contains_key("Main.RangeOptions.step%default"));
    assert!(before.contains_key("Main.Shape.Circle.id%default"));
}

/// A literal that gives every field, and a named construction that does,
/// are the terms they were before the type had defaults: the same hashes.
#[test]
fn literals_giving_every_field_keep_their_hashes() {
    let text = r#"
type RangeOptions = {
  start: Nat DEFAULT,
  stop: Nat,
  step: Nat
}

type Shape =
  | Circle (radius: Nat) (id: Text DEFAULT2)

def literal: RangeOptions := { start = 2, stop = 10, step = 3 }
def construction: Shape := Circle { id = "a", radius = 1 }
def positional: Shape := Circle 1 "a"
"#;
    let plain = hashes_by_name(&text.replace("DEFAULT2", "").replace("DEFAULT", ""));
    let defaulted = hashes_by_name(
        &text
            .replace("DEFAULT2", ":= \"anonymous\"")
            .replace("DEFAULT", ":= 0"),
    );
    for name in [
        "data Main.RangeOptions",
        "data Main.Shape",
        "Main.literal",
        "Main.construction",
        "Main.positional",
    ] {
        assert!(plain.contains_key(name), "{name}: {plain:#?}");
        assert_eq!(plain.get(name), defaulted.get(name), "{name}");
    }
}

/// A written field that a default uses is computed once: bound by a `let`
/// unless it's a variable or a literal (§5.1 rule 1).
#[test]
fn a_default_uses_a_written_field_through_a_let() {
    let text = r#"
type Twice = { x: Nat, twice: Nat := x + x }

def computed (n: Nat): Twice := { x = n * 3 }
def variable (n: Nat): Twice := { x = n }
def literal: Twice := { x = 4 }
def unused (n: Nat): Twice := { x = n * 3, twice = 1 }
"#;
    let (session, _) = load("twice.sw", text).expect("the file loads");
    let g = &session.elab.globals;
    let has_let = |name: &str| {
        let def = g
            .defs
            .iter()
            .find(|d| d.name.as_ref() == name)
            .unwrap_or_else(|| panic!("{name} is defined"));
        let body = def.body().expect("checked");
        body.subterms().any(|(t, _)| matches!(t, Term::Let(..)))
    };
    assert!(has_let("computed"));
    assert!(!has_let("variable"));
    assert!(!has_let("literal"));
    assert!(!has_let("unused"));
}

/// A lambda whose type is known only from the type expected of the call is
/// checked after that comparison when every argument is named, as when
/// none is.
#[test]
fn a_call_named_throughout_checks_its_lambdas_against_the_expected_type() {
    let text = r#"
import Std (List)

type Item = { id: Nat, size: Nat }

def ids (items: List Item): List Nat :=
  List.zipWith items (List.scanLeft items 0 (offset item => offset + item.size)) (item offset => item)
    |> List.map (f := item => item.id)

theorem positional (items: List Item): ids items = List.map items (item => item.id) :=
  List.mapZipWithScanLeft (item => item.id) (item => item.id) (item offset => item) (item offset => rfl)
    items 0 (offset item => offset + item.size)

theorem named (items: List Item): ids items = List.map items (item => item.id) :=
  List.mapZipWithScanLeft (h := item => item.id) (k := item => item.id) (g := item offset => item)
    (same := item offset => rfl) (xs := items) (z := 0) (f := offset item => offset + item.size)
"#;
    let (_, hashes) = load("named-late.sw", text).unwrap_or_else(|e| panic!("{e}"));
    let hash = |name: &str| {
        &hashes
            .iter()
            .find(|(n, _)| n.ends_with(name))
            .expect(name)
            .1
    };
    assert_eq!(hash("positional"), hash("named"));
}

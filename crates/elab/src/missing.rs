//! The cases a `match` leaves out, as arms to paste (SW-1027).
//!
//! The case tree has a `Tree::Missing` node for each constructor no arm
//! matches. [`annotate`] writes into each the pattern row it stands for,
//! from the splits above it; the checker, which alone knows whether the
//! constructor can be there (docs/proposals/indexed-families.md §7.3),
//! reports the ones that can as `E-NONEXHAUSTIVE` errors of one case each,
//! and [`merge`] folds the errors of one `match` into one that lists every
//! case.

use stitchwort_core::collections::{HashMap, HashSet};

use num_bigint::BigUint;
use stitchwort_core::DataId;
use stitchwort_core::registry::Builtin;
use stitchwort_syntax::{Diagnostic, MissingCases, Span};

use crate::{Elaborator, Result, Tree};

/// One case no arm matches, in a `Tree::Missing`.
#[derive(Clone, Debug, Default)]
pub(crate) struct Arm {
    /// The patterns of the arm that would cover it, one per scrutinee.
    pub pattern: String,
    /// The constructor taken at each split above it.
    pub order: Vec<usize>,
    /// Whether it is certainly missing: no index or other column can make
    /// it impossible, so the compiler reports it without checking.
    pub definite: bool,
    /// The condition of a guarded arm this case is reached through when it
    /// fails, if any: that arm covers nothing.
    pub guard: Option<Span>,
    /// For the numbers no arm of a number case matches: the message that
    /// lists the ones that are matched, which says more than a pattern `_`.
    pub other_numbers: Option<String>,
}

impl Arm {
    /// The case of the numbers a number case has no arm for, which `message`
    /// describes.
    pub(crate) fn other_numbers(message: String) -> Arm {
        Arm {
            definite: true,
            other_numbers: Some(message),
            ..Arm::default()
        }
    }

    /// The error for this case alone, at the `match` at `span`.
    pub(crate) fn diagnostic(&self, span: Span) -> Diagnostic {
        match &self.other_numbers {
            Some(message) => number_diagnostic(span, message.clone()),
            None => diagnostic(span, vec![(self.order.clone(), self.pattern.clone())]),
        }
    }

    /// The case left when the guarded arm whose condition is at `guard`
    /// fails and no row follows it.
    pub(crate) fn through_guard(guard: Span) -> Arm {
        Arm {
            definite: true,
            guard: Some(guard),
            ..Arm::default()
        }
    }

    pub(crate) fn definite() -> Arm {
        Arm {
            definite: true,
            ..Arm::default()
        }
    }
}

/// What a column holds in a branch of the tree.
enum Shape {
    /// Constructor `c` of `d`, its fields bound at levels from `base`.
    Ctor {
        d: DataId,
        c: usize,
        base: usize,
    },
    Num(BigUint),
}

fn number_diagnostic(span: Span, message: String) -> Diagnostic {
    Diagnostic::error("E-NONEXHAUSTIVE", message.clone())
        .with_label(span, message)
        .with_note("add an arm with a variable or `_` in that position")
}

/// The error for the cases `cases` (each with its place in the tree): one
/// message listing them as arms, and the `missing` data for the index.
pub(crate) fn diagnostic(span: Span, cases: Vec<(Vec<usize>, String)>) -> Diagnostic {
    let mut d = Diagnostic::error("E-NONEXHAUSTIVE", "").with_label(span, "");
    d.detail_mut().missing = Some(MissingCases::default());
    describe(&mut d, cases);
    d
}

/// Sets `d`'s message, label and `missing` to list `cases`: sorted in tree
/// order, each once, and the first [`MissingCases::CAP`] shown. A case's
/// text is its [`MissingCases::fills`] form, with the field names marked.
fn describe(d: &mut Diagnostic, mut cases: Vec<(Vec<usize>, String)>) {
    cases.sort();
    let mut seen = HashSet::default();
    cases.retain(|(_, p)| seen.insert(p.clone()));
    let missing = MissingCases {
        order: cases.iter().map(|(o, _)| o.clone()).collect(),
        patterns: cases.iter().map(|(_, p)| unmarked(p)).collect(),
        fills: cases.into_iter().map(|(_, p)| p).collect(),
    };
    let headline = match missing.patterns.as_slice() {
        [one] => format!("missing case: no arm matches `{one}`"),
        many => format!("missing cases: no arm matches {} patterns", many.len()),
    };
    let mut message = headline.clone();
    for p in missing.shown() {
        message.push_str(&format!("\n| {p} => ?"));
    }
    if missing.more() > 0 {
        message.push_str(&format!("\nand {} more", missing.more()));
    }
    d.message = message;
    if let Some(label) = d.labels.first_mut() {
        label.message = headline;
    }
    d.detail_mut().missing = Some(missing);
}

/// Folds the `E-NONEXHAUSTIVE` errors that list missing cases and are for
/// the same `match` (the same span) into one, the first's, listing them
/// all. They are the failed branches of one case: the error `f` returned
/// and the ones it left in `branch_errors` from index `start`.
pub(crate) fn merge<T>(cx: &crate::check::Ctx, start: usize, result: Result<T>) -> Result<T> {
    let Err(first) = result else {
        return result;
    };
    let mut all = vec![first];
    {
        let mut extra = cx.e.attempt.branch_errors.borrow_mut();
        let at = start.min(extra.len());
        all.extend(extra.drain(at..));
    }
    let mut kept = fold(all).into_iter();
    let first = kept.next().expect("the error returned");
    cx.e.attempt.branch_errors.borrow_mut().extend(kept);
    Err(first)
}

/// The hole for a field called `name`: `‹name›` when that is a name the
/// editor can bind a variable to (not a generated one), else `_`.
fn hole(name: &str) -> String {
    let usable = name.starts_with(|c: char| c.is_lowercase())
        && name.chars().all(|c| c.is_alphanumeric() || c == '_');
    if usable {
        format!("‹{name}›")
    } else {
        "_".to_string()
    }
}

/// `text` with each field name marker (`‹name›`) written as `_`.
fn unmarked(text: &str) -> String {
    let mut out = String::with_capacity(text.len());
    let mut skipping = false;
    for c in text.chars() {
        match c {
            '‹' => {
                skipping = true;
                out.push('_');
            }
            '›' => skipping = false,
            _ if !skipping => out.push(c),
            _ => {}
        }
    }
    out
}

/// Whether `d` lists missing cases.
pub(crate) fn listed(d: &Diagnostic) -> bool {
    d.code == "E-NONEXHAUSTIVE" && d.missing_data().is_some()
}

/// `all`, with the errors that list missing cases and are for the same
/// `match` (the same span) made one, at the first's place, listing them
/// all.
pub(crate) fn fold(all: Vec<Diagnostic>) -> Vec<Diagnostic> {
    let mut kept: Vec<Diagnostic> = Vec::new();
    let mut cases: Vec<Vec<(Vec<usize>, String)>> = Vec::new();
    let mut joined: Vec<bool> = Vec::new();
    for d in all {
        let own = |d: &Diagnostic| -> Vec<(Vec<usize>, String)> {
            let m = d.missing_data().expect("listed");
            m.order
                .iter()
                .cloned()
                .zip(m.fills.iter().cloned())
                .collect()
        };
        let slot = if listed(&d) {
            kept.iter()
                .position(|k| listed(k) && k.primary_span() == d.primary_span())
        } else {
            None
        };
        match slot {
            Some(i) => {
                cases[i].extend(own(&d));
                joined[i] = true;
            }
            None => {
                joined.push(false);
                cases.push(if listed(&d) { own(&d) } else { Vec::new() });
                kept.push(d);
            }
        }
    }
    for ((d, cs), joined) in kept.iter_mut().zip(cases).zip(joined) {
        // One that took none in is left as it is: it may have been worded
        // for the construct it is in (`in_context`).
        if joined {
            if cs.len() > 1 {
                // The note names one constructor.
                d.notes.clear();
            }
            describe(d, cs);
        }
    }
    kept
}

impl Elaborator {
    /// The patterns that split a value of data type `d`, one per
    /// constructor, in the form of [`MissingCases::fills`]: a list as `[]`
    /// and `[_, .._]`, a pair as `(_, _)`, a field with a declared name as
    /// `‹name›`. Constructors are written as they resolve at the current
    /// spot ([`Elaborator::ctor_written`]). `None` for an indexed family
    /// (some constructors may not fit) and for a proposition.
    pub fn constructor_patterns(&self, d: DataId) -> Option<Vec<String>> {
        let g = &self.ev();
        let reg = g.env.registry();
        let data = g.data(d);
        if !data.indices().is_empty()
            || data.ctors().is_empty()
            || data.sort() == stitchwort_core::Sort::Prop
        {
            return None;
        }
        let non_empty = reg.loaded_data(Builtin::NonEmptyList) == Some(d);
        let mut out = Vec::new();
        for (c, ctor) in data.ctors().iter().enumerate() {
            let here = Some((d, c));
            let fields: Vec<usize> = (0..ctor.fields.len())
                .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                .collect();
            out.push(if reg.ctor(Builtin::Nil) == here {
                "[]".to_string()
            } else if (non_empty || reg.ctor(Builtin::Cons) == here) && fields.len() == 2 {
                "[_, .._]".to_string()
            } else if reg.ctor(Builtin::MkPair) == here && fields.len() == 2 {
                "(_, _)".to_string()
            } else if reg.ctor(Builtin::UnitValue) == here {
                "()".to_string()
            } else {
                let mut text = self.ctor_written(d, c);
                for i in fields {
                    text.push(' ');
                    text.push_str(&hole(&ctor.fields[i].0));
                }
                text
            });
        }
        Some(out)
    }

    /// Constructor `c` of `d` as a pattern here can write it: its short
    /// name when that means it (`S` after `import Sf.Nat (Nat, S)`, or the
    /// prelude's own), else qualified by its type (`Nat.Succ`, or the type's
    /// full key), so that a program's own type that shares a name with
    /// another one is not confused with it.
    pub(crate) fn ctor_written(&self, d: DataId, c: usize) -> String {
        let g = &self.ev();
        let short = g.data(d).ctors()[c].name.to_string();
        let data_short = g.data(d).name().to_string();
        let full = format!(
            "{}.{short}",
            stitchwort_core::pretty::NameScope::full_name(
                self,
                stitchwort_core::pretty::Declaration::Data(d)
            )
        );
        for candidate in [short.clone(), format!("{data_short}.{short}"), full] {
            if let crate::scope::Resolved::Found {
                global: crate::Global::Ctor(d2, c2),
                rest,
                ..
            } = self.resolve_any(&candidate)
                && (d2, c2) == (d, c)
                && rest.is_empty()
            {
                return candidate;
            }
        }
        short
    }

    /// Writes into each `Tree::Missing` the pattern row it stands for.
    /// `root` is the levels of the columns the tree splits.
    pub(crate) fn annotate(&self, tree: &mut Tree, root: &[usize]) {
        let mut shapes = HashMap::default();
        self.annotate_in(tree, root, &mut shapes, &mut Vec::new());
    }

    fn annotate_in(
        &self,
        tree: &mut Tree,
        root: &[usize],
        shapes: &mut HashMap<usize, Shape>,
        path: &mut Vec<usize>,
    ) {
        match tree {
            Tree::Leaf { .. } | Tree::Absurd { .. } => {}
            Tree::Guard { otherwise, .. } => self.annotate_in(otherwise, root, shapes, path),
            Tree::Missing { arm, .. } => {
                arm.pattern = (root.iter())
                    .map(|&level| self.show_column(level, shapes, false))
                    .collect::<Vec<_>>()
                    .join(", ");
                arm.order = path.clone();
            }
            Tree::Case {
                level,
                data,
                branches,
                depth,
                ..
            } => {
                for (c, (_, subtree)) in branches.iter_mut().enumerate() {
                    // What the siblings bound at these levels is gone.
                    shapes.retain(|l, _| *l < *depth);
                    shapes.insert(
                        *level,
                        Shape::Ctor {
                            d: *data,
                            c,
                            base: *depth,
                        },
                    );
                    path.push(c);
                    self.annotate_in(subtree, root, shapes, path);
                    path.pop();
                }
                shapes.retain(|l, _| *l < *depth);
                shapes.remove(level);
            }
            Tree::NumCase {
                level,
                arms,
                default,
                ..
            } => {
                for (n, subtree) in arms.iter_mut() {
                    shapes.insert(*level, Shape::Num(n.clone()));
                    self.annotate_in(subtree, root, shapes, path);
                }
                shapes.remove(level);
                self.annotate_in(default, root, shapes, path);
            }
        }
    }

    /// The pattern for the value at `level`: `_` where no split looked at
    /// it. `atom` when it is an argument, so a constructor with arguments
    /// is in parentheses.
    fn show_column(&self, level: usize, shapes: &HashMap<usize, Shape>, atom: bool) -> String {
        let g = &self.ev();
        let reg = &g.env.registry();
        let (d, c, base) = match shapes.get(&level) {
            None => return "_".to_string(),
            Some(Shape::Num(n)) => return n.to_string(),
            Some(Shape::Ctor { d, c, base }) => (*d, *c, *base),
        };
        let ctor = &g.data(d).ctors()[c];
        // The fields a pattern writes: the explicit ones.
        let fields: Vec<usize> = (0..ctor.fields.len())
            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
            .map(|i| base + i)
            .collect();
        let shown = |l: usize| self.show_column(l, shapes, true);
        let here = Some((d, c));
        if reg.ctor(Builtin::Nil) == here {
            return "[]".to_string();
        }
        // A `NonEmptyList` is matched with list patterns (`[x, ..rest]`), so
        // it's shown as one: its head, then its tail's elements.
        let non_empty = reg.loaded_data(Builtin::NonEmptyList) == Some(d);
        if (non_empty || reg.ctor(Builtin::Cons) == here) && fields.len() == 2 {
            // `[a, b, ..]`: the elements down to the end, which is `[]`, or
            // a tail nothing looked at.
            let mut items = vec![self.show_column(fields[0], shapes, false)];
            let mut tail = fields[1];
            loop {
                match shapes.get(&tail) {
                    Some(Shape::Ctor { d, c, base })
                        if reg.ctor(Builtin::Cons) == Some((*d, *c)) =>
                    {
                        let ctor = &g.data(*d).ctors()[*c];
                        let explicit: Vec<usize> = (0..ctor.fields.len())
                            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                            .map(|i| base + i)
                            .collect();
                        if explicit.len() != 2 {
                            break;
                        }
                        items.push(self.show_column(explicit[0], shapes, false));
                        tail = explicit[1];
                    }
                    Some(Shape::Ctor { d, c, .. }) if reg.ctor(Builtin::Nil) == Some((*d, *c)) => {
                        return format!("[{}]", items.join(", "));
                    }
                    _ => break,
                }
            }
            return format!("[{}, .._]", items.join(", "));
        }
        if reg.ctor(Builtin::MkPair) == here && fields.len() == 2 {
            // Three or more nest to the right: `(a, b, c)`.
            let mut items = vec![self.show_column(fields[0], shapes, false)];
            let mut rest = fields[1];
            loop {
                match shapes.get(&rest) {
                    Some(Shape::Ctor { d, c, base })
                        if reg.ctor(Builtin::MkPair) == Some((*d, *c)) =>
                    {
                        let ctor = &g.data(*d).ctors()[*c];
                        let explicit: Vec<usize> = (0..ctor.fields.len())
                            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
                            .map(|i| base + i)
                            .collect();
                        if explicit.len() != 2 {
                            break;
                        }
                        items.push(self.show_column(explicit[0], shapes, false));
                        rest = explicit[1];
                    }
                    _ => break,
                }
            }
            items.push(self.show_column(rest, shapes, false));
            return format!("({})", items.join(", "));
        }
        if reg.ctor(Builtin::UnitValue) == here {
            return "()".to_string();
        }
        let args: Vec<String> = (0..ctor.fields.len())
            .filter(|&i| !ctor.implicit.get(i).copied().unwrap_or(false))
            .map(|i| {
                let arg = shown(base + i);
                if arg == "_" {
                    hole(&ctor.fields[i].0)
                } else {
                    arg
                }
            })
            .collect();
        let written = self.ctor_written(d, c);
        if args.is_empty() {
            return written;
        }
        let text = format!("{written} {}", args.join(" "));
        if atom { format!("({text})") } else { text }
    }
}

/// The error for the cases of `tree` that are certainly missing, if any.
pub(crate) fn definite(tree: &Tree, span: Span) -> Option<Diagnostic> {
    /// The first number case in the tree: it is reported alone, as it was
    /// when coverage met it.
    fn numbers<'t>(tree: &'t Tree<'_>) -> Option<&'t Arm> {
        match tree {
            Tree::Leaf { .. } | Tree::Absurd { .. } => None,
            Tree::Guard { otherwise, .. } => numbers(otherwise),
            Tree::Missing { arm, .. } => arm.other_numbers.as_ref().map(|_| arm),
            Tree::Case { branches, .. } => branches.iter().find_map(|(_, t)| numbers(t)),
            Tree::NumCase { arms, default, .. } => (arms.iter())
                .find_map(|(_, t)| numbers(t))
                .or_else(|| numbers(default)),
        }
    }
    if let Some(arm) = numbers(tree) {
        return Some(arm.diagnostic(span));
    }
    fn collect(tree: &Tree, out: &mut Vec<(Vec<usize>, String)>, guards: &mut Vec<Span>) {
        match tree {
            Tree::Leaf { .. } | Tree::Absurd { .. } => {}
            Tree::Guard { otherwise, .. } => collect(otherwise, out, guards),
            Tree::Missing { arm, .. } => {
                if arm.definite {
                    out.push((arm.order.clone(), arm.pattern.clone()));
                    guards.extend(arm.guard);
                }
            }
            Tree::Case { branches, .. } => {
                branches.iter().for_each(|(_, t)| collect(t, out, guards))
            }
            Tree::NumCase { arms, default, .. } => {
                arms.iter().for_each(|(_, t)| collect(t, out, guards));
                collect(default, out, guards);
            }
        }
    }
    let mut cases = Vec::new();
    let mut guards = Vec::new();
    collect(tree, &mut cases, &mut guards);
    if cases.is_empty() {
        return None;
    }
    let mut d = diagnostic(span, cases);
    guards.dedup();
    if !guards.is_empty() {
        for guard in guards {
            d = d.with_label(guard, "this arm has a condition, so it covers nothing");
        }
        d = d.with_note(
            "an arm with `if` covers no case for sure: add an arm without `if` for these values",
        );
    }
    Some(d)
}

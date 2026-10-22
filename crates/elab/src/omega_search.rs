//! The search behind `omega` (docs/proposals/omega.md §6.6, §6.8): untrusted,
//! it only has to find a certificate that `Std.Omega.check` accepts. A wrong
//! answer here can lose a proof or waste time, never prove something false.
//!
//! The input is a list of rows `0 <= c + Σ a_i * x_i` over `n` atoms, each
//! from a source (a fact's row, the goal's negation, or `x_i >= 0`). The
//! search is Fourier–Motzkin: equalities (a row and its exact negation) are
//! used first to eliminate a variable, then variables are eliminated by
//! adding every lower bound to every upper bound, with every new row divided
//! by the gcd of its coefficients and its constant rounded down (`Divide`).
//! When every variable is gone without a contradiction the remaining rows
//! have a rational solution, found by substituting back; if it isn't whole,
//! the search splits on a fractional variable (`x <= v` or `x >= v + 1`) and
//! refutes both sides, a few levels deep at most. Everything is
//! deterministic: no hash map is iterated, and the budget counts rows.
//!
//! Each row remembers how it was made ([`Node`]), so a contradiction can be
//! written out as certificate steps ([`emit`]), each row once per branch.

use std::collections::HashMap;

/// `0 <= c + Σ a[i] * x_i`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub c: i128,
    pub a: Vec<i128>,
}

impl Row {
    pub(crate) fn zero(n: usize) -> Row {
        Row {
            c: 0,
            a: vec![0; n],
        }
    }

    fn is_closed(&self) -> bool {
        self.a.iter().all(|&x| x == 0)
    }
}

/// Where an input row comes from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Source {
    /// Row `i` of the facts, flattened (an equation has two).
    Input(usize),
    NegGoal,
    /// `x_i >= 0`.
    NonNeg(usize),
}

/// How a row was made.
#[derive(Clone, Debug)]
enum Node {
    Source(Source),
    /// A row a split adds (`l` on the left, `-1 - l` on the right) or one of
    /// the rows a case of a fact adds. Nothing else is written before a
    /// split, so it is the branch's row with this number.
    Split(usize),
    /// `Σ k * row`, every `k > 0`.
    Combine(Vec<(i128, usize)>),
    /// A row divided by `d > 0`, which divides every coefficient; the
    /// constant is rounded down.
    Divide(usize, i128),
}

/// The search's result for one refutation: a tree of branches, each closed by
/// a row whose coefficients are all 0 and whose constant is negative.
#[derive(Clone, Debug)]
enum Tree {
    Closed(usize),
    Split {
        l: Row,
        left: Box<Tree>,
        right: Box<Tree>,
    },
    /// The cases of `problem.cases[case]`.
    Cases {
        case: usize,
        left: Box<Tree>,
        right: Box<Tree>,
    },
}

/// A certificate as `Std.Omega.Cert` has it, with rows numbered from 0 in
/// each branch.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Cert {
    Close(usize),
    Then(Step, Box<Cert>),
    Split(Row, Box<Cert>, Box<Cert>),
    /// The cases of the fact with this number (in the caller's numbering).
    Cases(usize, Box<Cert>, Box<Cert>),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Step {
    Input(usize),
    NegGoal,
    NatNonneg(usize),
    Combine(Vec<(i128, usize)>),
    Divide(usize, i128),
}

/// A rational number, `n / d` with `d > 0` and no common factor.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Rat {
    pub n: i128,
    pub d: i128,
}

impl Rat {
    fn int(n: i128) -> Rat {
        Rat { n, d: 1 }
    }

    fn new(n: i128, d: i128) -> Option<Rat> {
        if d == 0 {
            return None;
        }
        let (n, d) = if d < 0 {
            (n.checked_neg()?, d.checked_neg()?)
        } else {
            (n, d)
        };
        let g = gcd(n, d).max(1);
        Some(Rat { n: n / g, d: d / g })
    }

    fn add(self, o: Rat) -> Option<Rat> {
        Rat::new(
            self.n
                .checked_mul(o.d)?
                .checked_add(o.n.checked_mul(self.d)?)?,
            self.d.checked_mul(o.d)?,
        )
    }

    fn mul_int(self, k: i128) -> Option<Rat> {
        Rat::new(self.n.checked_mul(k)?, self.d)
    }

    fn div_int(self, k: i128) -> Option<Rat> {
        Rat::new(self.n, self.d.checked_mul(k)?)
    }

    fn le(self, o: Rat) -> Option<bool> {
        Some(self.n.checked_mul(o.d)? <= o.n.checked_mul(self.d)?)
    }

    fn floor(self) -> i128 {
        self.n.div_euclid(self.d)
    }

    fn ceil(self) -> i128 {
        -(-self.n).div_euclid(self.d)
    }

    pub(crate) fn is_int(self) -> bool {
        self.d == 1
    }
}

impl std::fmt::Display for Rat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.d == 1 {
            write!(f, "{}", self.n)
        } else {
            write!(f, "{}/{}", self.n, self.d)
        }
    }
}

pub(crate) fn gcd(a: i128, b: i128) -> i128 {
    let (mut a, mut b) = (a.unsigned_abs(), b.unsigned_abs());
    while b != 0 {
        (a, b) = (b, a % b);
    }
    i128::try_from(a).unwrap_or(i128::MAX)
}

/// Why a search failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum Failure {
    /// Every branch tried had a whole-number solution: values for the atoms
    /// satisfying every row (a model of the abstraction, not necessarily of
    /// the real terms).
    Integer(Vec<Rat>),
    /// A rational solution that splitting didn't get rid of within its depth.
    Rational(Vec<Rat>),
    /// The row budget ran out (or a number grew too large).
    Budget,
}

/// The limits of one `omega`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Limits {
    /// Rows the whole search may make.
    pub rows: usize,
    /// How deep splits may nest.
    pub depth: usize,
}

pub(crate) const LIMITS: Limits = Limits {
    rows: 20_000,
    depth: 6,
};

struct Search<'p> {
    n: usize,
    nodes: Vec<(Node, Row)>,
    made: usize,
    limits: Limits,
    cases: &'p [Case],
}

/// The rows of one stage of elimination, at most one per coefficient list
/// (the strongest), with an index by coefficients.
#[derive(Default)]
struct Rows {
    ids: Vec<usize>,
    by: HashMap<Vec<i128>, usize>,
}

/// What one Fourier–Motzkin run found.
enum Fm {
    Contradiction(usize),
    Model(Vec<Rat>),
    Budget,
}

/// A step of elimination, for substituting back.
enum Elim {
    /// `x_var` was eliminated using equality row `row`.
    Eq { var: usize, row: usize },
    /// `x_var` was eliminated; these rows mentioned it.
    Ineq { var: usize, rows: Vec<usize> },
}

impl Search<'_> {
    fn push(&mut self, node: Node, row: Row) -> Option<usize> {
        self.made += 1;
        if self.made > self.limits.rows {
            return None;
        }
        self.nodes.push((node, row));
        Some(self.nodes.len() - 1)
    }

    fn row(&self, id: usize) -> &Row {
        &self.nodes[id].1
    }

    /// `Σ k * row`; `None` if a number overflows or the budget runs out.
    fn combine(&mut self, terms: Vec<(i128, usize)>) -> Option<usize> {
        let mut row = Row::zero(self.n);
        for &(k, id) in &terms {
            let r = &self.nodes[id].1;
            row.c = row.c.checked_add(k.checked_mul(r.c)?)?;
            for (x, &y) in row.a.iter_mut().zip(&r.a) {
                *x = x.checked_add(k.checked_mul(y)?)?;
            }
        }
        self.push(Node::Combine(terms), row)
    }

    /// The row divided by the gcd of its coefficients, if that's more than 1.
    fn tighten(&mut self, id: usize) -> Option<usize> {
        let r = self.row(id);
        let g = r.a.iter().fold(0, |g, &x| gcd(g, x));
        if g <= 1 {
            return Some(id);
        }
        let row = Row {
            c: r.c.div_euclid(g),
            a: r.a.iter().map(|&x| x / g).collect(),
        };
        self.push(Node::Divide(id, g), row)
    }

    /// One Fourier–Motzkin run over `start`.
    fn fm(&mut self, start: &[usize]) -> Fm {
        match self.fm_inner(start) {
            Some(result) => result,
            None => Fm::Budget,
        }
    }

    fn fm_inner(&mut self, start: &[usize]) -> Option<Fm> {
        let mut rows = Rows::default();
        for &id in start {
            if let Some(contra) = self.add_row(&mut rows, id)? {
                return Some(Fm::Contradiction(contra));
            }
        }
        let mut history: Vec<Elim> = Vec::new();
        loop {
            let active: Vec<usize> = (0..self.n)
                .filter(|&j| rows.ids.iter().any(|&r| self.row(r).a[j] != 0))
                .collect();
            if active.is_empty() {
                return Some(match self.back_substitute(&history) {
                    Some(model) => Fm::Model(model),
                    None => Fm::Budget,
                });
            }
            // Equalities first: a row whose exact negation is also a row.
            if let Some((pos, neg, var)) = self.find_equality(&rows) {
                let a = self.row(pos).a[var];
                let mut next = Rows::default();
                for &r in rows.ids.iter().filter(|&&r| r != pos && r != neg) {
                    let b = self.row(r).a[var];
                    if b == 0 {
                        if let Some(contra) = self.add_row(&mut next, r)? {
                            return Some(Fm::Contradiction(contra));
                        }
                        continue;
                    }
                    // Cancel with the side whose coefficient has the other sign.
                    let other = if (b > 0) == (a > 0) { neg } else { pos };
                    let (ka, kb) = (a.abs(), b.abs());
                    let g = gcd(ka, kb);
                    let id = self.combine(vec![(ka / g, r), (kb / g, other)])?;
                    let id = self.tighten(id)?;
                    if let Some(contra) = self.add_row(&mut next, id)? {
                        return Some(Fm::Contradiction(contra));
                    }
                }
                history.push(Elim::Eq { var, row: pos });
                rows = next;
                continue;
            }
            let var = self.choose(&rows.ids, &active);
            let (mut lower, mut upper, mut rest) = (Vec::new(), Vec::new(), Vec::new());
            for &r in &rows.ids {
                let a = self.row(r).a[var];
                if a > 0 {
                    lower.push(r);
                } else if a < 0 {
                    upper.push(r);
                } else {
                    rest.push(r);
                }
            }
            let mut next = Rows::default();
            for &r in &rest {
                if let Some(contra) = self.add_row(&mut next, r)? {
                    return Some(Fm::Contradiction(contra));
                }
            }
            for &p in &lower {
                for &q in &upper {
                    let a = self.row(p).a[var];
                    let b = -self.row(q).a[var];
                    let g = gcd(a, b);
                    let id = self.combine(vec![(b / g, p), (a / g, q)])?;
                    let id = self.tighten(id)?;
                    if let Some(contra) = self.add_row(&mut next, id)? {
                        return Some(Fm::Contradiction(contra));
                    }
                }
            }
            let mut mentioned = lower;
            mentioned.extend(upper);
            history.push(Elim::Ineq {
                var,
                rows: mentioned,
            });
            rows = next;
        }
    }

    /// Adds `id` (tightened) to `rows`, unless it's implied by a row there or
    /// trivially true; a contradiction, if it is one or contradicts a row
    /// there directly.
    fn add_row(&mut self, rows: &mut Rows, id: usize) -> Option<Option<usize>> {
        let id = self.tighten(id)?;
        let r = self.row(id).clone();
        if r.is_closed() {
            return Some((r.c < 0).then_some(id));
        }
        let neg: Vec<i128> = r.a.iter().map(|x| -x).collect();
        if let Some(&i) = rows.by.get(&neg) {
            let other = rows.ids[i];
            if self.row(other).c.checked_add(r.c)? < 0 {
                let contra = self.combine(vec![(1, other), (1, id)])?;
                return Some(Some(contra));
            }
        }
        if let Some(&i) = rows.by.get(&r.a) {
            if r.c < self.row(rows.ids[i]).c {
                rows.ids[i] = id;
            }
            return Some(None);
        }
        rows.by.insert(r.a, rows.ids.len());
        rows.ids.push(id);
        Some(None)
    }

    /// An equality among `rows`: the row with a positive coefficient for the
    /// variable to eliminate, its negation, and the variable, choosing the
    /// smallest coefficient.
    fn find_equality(&self, rows: &Rows) -> Option<(usize, usize, usize)> {
        let mut best: Option<(i128, usize, usize, usize)> = None;
        for &r in &rows.ids {
            let row = self.row(r);
            let neg: Vec<i128> = row.a.iter().map(|x| -x).collect();
            let Some(&q) = rows.by.get(&neg).map(|&i| &rows.ids[i]) else {
                continue;
            };
            if row.c.checked_add(self.row(q).c) != Some(0) {
                continue;
            }
            for (j, &a) in row.a.iter().enumerate() {
                if a > 0 && best.is_none_or(|(b, ..)| a < b) {
                    best = Some((a, r, q, j));
                }
            }
        }
        best.map(|(_, p, q, j)| (p, q, j))
    }

    /// The variable to eliminate: one with bounds on one side only if there
    /// is one (dropping its rows loses nothing), else the one making the
    /// fewest new rows, preferring one whose bounds on some side all have
    /// coefficient 1 (an exact elimination), then the lowest index.
    fn choose(&self, rows: &[usize], active: &[usize]) -> usize {
        let mut best: Option<((usize, bool, usize), usize)> = None;
        for &j in active {
            let (mut p, mut q, mut unit_p, mut unit_q) = (0usize, 0usize, true, true);
            for &r in rows {
                let a = self.row(r).a[j];
                if a > 0 {
                    p += 1;
                    unit_p &= a == 1;
                } else if a < 0 {
                    q += 1;
                    unit_q &= a == -1;
                }
            }
            let cost = if p == 0 || q == 0 { 0 } else { p * q };
            let key = (cost, !(unit_p || unit_q), j);
            if best.is_none_or(|(k, _)| key < k) {
                best = Some((key, j));
            }
        }
        best.expect("an active variable").1
    }

    /// A rational point satisfying every row, from the eliminations in
    /// reverse: each variable takes the smallest whole value its bounds allow,
    /// or the lower bound itself if there's none between them.
    fn back_substitute(&self, history: &[Elim]) -> Option<Vec<Rat>> {
        let mut x: Vec<Option<Rat>> = vec![None; self.n];
        let value = |x: &mut Vec<Option<Rat>>, row: &Row, skip: usize| -> Option<Rat> {
            let mut sum = Rat::int(row.c);
            for (j, &a) in row.a.iter().enumerate() {
                if j == skip || a == 0 {
                    continue;
                }
                let v = *x[j].get_or_insert(Rat::int(0));
                sum = sum.add(v.mul_int(a)?)?;
            }
            Some(sum)
        };
        for elim in history.iter().rev() {
            match elim {
                Elim::Eq { var, row } => {
                    let r = self.row(*row);
                    let rest = value(&mut x, r, *var)?;
                    x[*var] = Some(rest.mul_int(-1)?.div_int(r.a[*var])?);
                }
                Elim::Ineq { var, rows } => {
                    let (mut lo, mut hi): (Option<Rat>, Option<Rat>) = (None, None);
                    for &id in rows {
                        let r = self.row(id);
                        let a = r.a[*var];
                        let rest = value(&mut x, r, *var)?;
                        if a > 0 {
                            let b = rest.mul_int(-1)?.div_int(a)?;
                            if lo.is_none_or(|l| l.le(b) == Some(true)) {
                                lo = Some(b);
                            }
                        } else {
                            let b = rest.div_int(-a)?;
                            if hi.is_none_or(|h| b.le(h) == Some(true)) {
                                hi = Some(b);
                            }
                        }
                    }
                    let v = match (lo, hi) {
                        (Some(l), Some(h)) => {
                            let c = Rat::int(l.ceil());
                            if c.le(h)? { c } else { l }
                        }
                        (Some(l), None) => Rat::int(l.ceil()),
                        (None, Some(h)) => Rat::int(h.floor().min(0)),
                        (None, None) => Rat::int(0),
                    };
                    x[*var] = Some(v);
                }
            }
        }
        Some(x.into_iter().map(|v| v.unwrap_or(Rat::int(0))).collect())
    }

    /// Refutes `base` plus the split rows `splits` (ancestors' first). When
    /// the rows have a solution, it splits: first on a fact with cases (from
    /// `cases`, not yet split on here) whose cases the solution both
    /// violates, otherwise on a variable whose value is fractional.
    fn refute(
        &mut self,
        base: &[usize],
        cases: &[usize],
        splits: &mut Vec<usize>,
        depth: usize,
        used: &mut Vec<usize>,
    ) -> Result<Tree, Failure> {
        let mut start = base.to_vec();
        start.extend(splits.iter().copied());
        let model = match self.fm(&start) {
            Fm::Contradiction(id) => return Ok(Tree::Closed(id)),
            Fm::Budget => return Err(Failure::Budget),
            Fm::Model(model) => model,
        };
        let case = cases.iter().copied().find(|&k| {
            !used.contains(&k)
                && !holds_all(&self.cases[k].left, &model)
                && !holds_all(&self.cases[k].right, &model)
        });
        let fractional = model.iter().position(|v| !v.is_int());
        if case.is_none() && fractional.is_none() {
            return Err(Failure::Integer(model));
        }
        if depth >= self.limits.depth {
            return Err(if fractional.is_some() {
                Failure::Rational(model)
            } else {
                Failure::Integer(model)
            });
        }
        if let Some(k) = case {
            used.push(k);
            let left_rows = self.cases[k].left.clone();
            let right_rows = self.cases[k].right.clone();
            let left = self.refute_with(base, cases, splits, depth, used, &left_rows);
            let right = match &left {
                Ok(_) => self.refute_with(base, cases, splits, depth, used, &right_rows),
                Err(_) => Err(Failure::Budget),
            };
            used.pop();
            let left = left?;
            return Ok(Tree::Cases {
                case: k,
                left: Box::new(left),
                right: Box::new(right?),
            });
        }
        let j = fractional.expect("a fractional value");
        // `v - x_j >= 0` on the left, `x_j - v - 1 >= 0` on the right.
        let v = model[j].floor();
        let mut l = Row::zero(self.n);
        l.c = v;
        l.a[j] = -1;
        let mut other = Row::zero(self.n);
        other.c = -1 - v;
        other.a[j] = 1;
        let left = self.refute_with(base, cases, splits, depth, used, std::slice::from_ref(&l))?;
        let right = self.refute_with(base, cases, splits, depth, used, &[other])?;
        Ok(Tree::Split {
            l,
            left: Box::new(left),
            right: Box::new(right),
        })
    }

    /// [`Search::refute`] one level down, with `rows` added as split rows.
    fn refute_with(
        &mut self,
        base: &[usize],
        cases: &[usize],
        splits: &mut Vec<usize>,
        depth: usize,
        used: &mut Vec<usize>,
        rows: &[Row],
    ) -> Result<Tree, Failure> {
        let mark = splits.len();
        for row in rows {
            let Some(id) = self.push(Node::Split(splits.len()), row.clone()) else {
                splits.truncate(mark);
                return Err(Failure::Budget);
            };
            splits.push(id);
        }
        let tree = self.refute(base, cases, splits, depth + 1, used);
        splits.truncate(mark);
        tree
    }

    /// The certificate for `tree`, below `depth` rows added by splits.
    fn emit(&self, tree: &Tree, depth: usize) -> Cert {
        match tree {
            Tree::Split { l, left, right } => Cert::Split(
                l.clone(),
                Box::new(self.emit(left, depth + 1)),
                Box::new(self.emit(right, depth + 1)),
            ),
            Tree::Cases { case, left, right } => {
                let c = &self.cases[*case];
                Cert::Cases(
                    c.fact,
                    Box::new(self.emit(left, depth + c.left.len())),
                    Box::new(self.emit(right, depth + c.right.len())),
                )
            }
            Tree::Closed(id) => {
                let mut numbers: HashMap<usize, usize> = HashMap::new();
                let mut steps: Vec<Step> = Vec::new();
                let last = self.write(*id, depth, &mut numbers, &mut steps);
                let mut cert = Cert::Close(last);
                for step in steps.into_iter().rev() {
                    cert = Cert::Then(step, Box::new(cert));
                }
                cert
            }
        }
    }

    /// Writes the steps making row `id` (and the rows it needs, first), and
    /// returns its number. Split rows are numbered by depth, before any step.
    fn write(
        &self,
        id: usize,
        depth: usize,
        numbers: &mut HashMap<usize, usize>,
        steps: &mut Vec<Step>,
    ) -> usize {
        if let Node::Split(d) = &self.nodes[id].0 {
            return *d;
        }
        if let Some(&n) = numbers.get(&id) {
            return n;
        }
        let step = match &self.nodes[id].0 {
            Node::Source(Source::Input(i)) => Step::Input(*i),
            Node::Source(Source::NegGoal) => Step::NegGoal,
            Node::Source(Source::NonNeg(i)) => Step::NatNonneg(*i),
            Node::Combine(terms) => {
                let terms = terms
                    .iter()
                    .map(|&(k, r)| (k, self.write(r, depth, numbers, steps)))
                    .collect();
                Step::Combine(terms)
            }
            Node::Divide(r, d) => Step::Divide(self.write(*r, depth, numbers, steps), *d),
            Node::Split(_) => unreachable!("handled above"),
        };
        steps.push(step);
        let n = depth + steps.len() - 1;
        numbers.insert(id, n);
        n
    }
}

/// One refutation problem: the input rows, each with its source, over `n`
/// atoms, and the facts with cases.
pub(crate) struct Problem {
    pub n: usize,
    pub rows: Vec<(Source, Row)>,
    pub cases: Vec<Case>,
}

/// A fact with two cases (`Std.Omega.Fact.left`/`right`): `t = a - b`, `max`,
/// `min`, `a != b`. Each case is the rows it adds.
#[derive(Clone, Debug)]
pub(crate) struct Case {
    /// The fact's number, which the certificate names.
    pub fact: usize,
    pub left: Vec<Row>,
    pub right: Vec<Row>,
}

impl Case {
    /// The atoms either case mentions, as a row of 0s and 1s.
    fn atoms(&self, n: usize) -> Row {
        Row {
            c: 0,
            a: (0..n)
                .map(|j| i128::from(self.left.iter().chain(&self.right).any(|r| r.a[j] != 0)))
                .collect(),
        }
    }
}

/// Whether `model` satisfies every row.
fn holds_all(rows: &[Row], model: &[Rat]) -> bool {
    rows.iter().all(|r| {
        let mut sum = Rat::int(r.c);
        for (j, &a) in r.a.iter().enumerate() {
            if a == 0 {
                continue;
            }
            match model[j].mul_int(a).and_then(|v| sum.add(v)) {
                Some(v) => sum = v,
                None => return false,
            }
        }
        Rat::int(0).le(sum) == Some(true)
    })
}

/// Refutes `problem`: the rows connected to the goal's negation first (with
/// every closed row), then each other group of rows sharing atoms on its
/// own, since a contradiction among facts unrelated to the goal proves it
/// too. Each attempt adds `x >= 0` for its atoms. A failure reports the
/// goal's attempt, with every attempt's model merged.
pub(crate) fn refute(problem: &Problem, limits: Limits) -> Result<Cert, Failure> {
    let n = problem.n;
    let mut search = Search {
        n,
        nodes: Vec::new(),
        made: 0,
        limits,
        cases: &problem.cases,
    };
    let mut parent: Vec<usize> = (0..n).collect();
    fn find(parent: &mut [usize], mut i: usize) -> usize {
        while parent[i] != i {
            parent[i] = parent[parent[i]];
            i = parent[i];
        }
        i
    }
    // A fact with cases joins every atom of both cases.
    let joins: Vec<Row> = problem
        .rows
        .iter()
        .map(|(_, r)| r.clone())
        .chain(problem.cases.iter().map(|c| c.atoms(n)))
        .collect();
    for row in &joins {
        let atoms: Vec<usize> = (0..n).filter(|&j| row.a[j] != 0).collect();
        for w in atoms.windows(2) {
            let (a, b) = (find(&mut parent, w[0]), find(&mut parent, w[1]));
            parent[a] = b;
        }
    }
    let ids: Vec<usize> = problem
        .rows
        .iter()
        .map(|(source, row)| {
            search.nodes.push((Node::Source(*source), row.clone()));
            search.nodes.len() - 1
        })
        .collect();
    let component = |parent: &mut Vec<usize>, row: &Row| -> Option<usize> {
        (0..n).find(|&j| row.a[j] != 0).map(|j| find(parent, j))
    };
    // The groups to try, in order: the goal's first (if there's a goal).
    let mut order: Vec<Option<usize>> = Vec::new();
    for (source, row) in &problem.rows {
        if *source == Source::NegGoal {
            order.push(component(&mut parent, row));
        }
    }
    for (_, row) in &problem.rows {
        let c = component(&mut parent, row);
        if c.is_some() && !order.contains(&c) {
            order.push(c);
        }
    }
    if order.is_empty() {
        order.push(None);
    }
    let goal_group = problem
        .rows
        .iter()
        .find(|(s, _)| *s == Source::NegGoal)
        .map(|(_, row)| component(&mut parent, row));
    let mut first_failure: Option<Failure> = None;
    let mut merged: Vec<Rat> = vec![Rat::int(0); n];
    let mut rational = false;
    for group in order {
        let mut base: Vec<usize> = Vec::new();
        let mut atoms: Vec<usize> = Vec::new();
        for (k, (source, row)) in problem.rows.iter().enumerate() {
            let c = component(&mut parent, row);
            // A goal with no atoms belongs with the closed rows.
            let in_group = c == group || c.is_none();
            if !in_group {
                continue;
            }
            if *source == Source::NegGoal && goal_group != Some(group) {
                continue;
            }
            base.push(ids[k]);
            atoms.extend((0..n).filter(|&j| row.a[j] != 0));
        }
        let mut cases: Vec<usize> = Vec::new();
        for (k, c) in problem.cases.iter().enumerate() {
            let joined = c.atoms(n);
            let g = component(&mut parent, &joined);
            if g == group || g.is_none() {
                cases.push(k);
                atoms.extend((0..n).filter(|&j| joined.a[j] != 0));
            }
        }
        atoms.sort_unstable();
        atoms.dedup();
        for j in atoms {
            let mut row = Row::zero(n);
            row.a[j] = 1;
            match search.push(Node::Source(Source::NonNeg(j)), row) {
                Some(id) => base.push(id),
                None => return Err(Failure::Budget),
            }
        }
        match search.refute(&base, &cases, &mut Vec::new(), 0, &mut Vec::new()) {
            Ok(tree) => return Ok(search.emit(&tree, 0)),
            Err(Failure::Budget) => return Err(Failure::Budget),
            Err(failure) => {
                let model = match &failure {
                    Failure::Integer(m) => m,
                    Failure::Rational(m) => {
                        rational = true;
                        m
                    }
                    Failure::Budget => unreachable!(),
                };
                for (j, v) in model.iter().enumerate() {
                    if group.is_some_and(|g| find(&mut parent, j) == g) {
                        merged[j] = *v;
                    }
                }
                first_failure.get_or_insert(failure);
            }
        }
    }
    Err(match first_failure {
        Some(_) if rational => Failure::Rational(merged),
        Some(_) => Failure::Integer(merged),
        None => Failure::Budget,
    })
}

/// Replays a certificate over the input rows the way `Std.Omega.check` does,
/// for tests and as a cheap guard before the kernel runs the real checker.
pub(crate) fn replay(problem: &Problem, cert: &Cert) -> bool {
    let n = problem.n;
    let input = |i: usize| -> Option<Row> {
        problem
            .rows
            .iter()
            .filter(|(s, _)| matches!(s, Source::Input(_)))
            .find(|(s, _)| *s == Source::Input(i))
            .map(|(_, r)| r.clone())
    };
    let neg = problem
        .rows
        .iter()
        .find(|(s, _)| *s == Source::NegGoal)
        .map(|(_, r)| r.clone());
    fn go(
        n: usize,
        input: &dyn Fn(usize) -> Option<Row>,
        neg: &Option<Row>,
        cases: &[Case],
        ctx: &mut Vec<Row>,
        cert: &Cert,
    ) -> bool {
        match cert {
            Cert::Close(r) => ctx
                .get(*r)
                .is_some_and(|row| row.c < 0 && row.a.iter().all(|&x| x == 0)),
            Cert::Then(step, rest) => {
                let row = match step {
                    Step::Input(i) => match input(*i) {
                        Some(r) => r,
                        None => return false,
                    },
                    Step::NegGoal => match neg {
                        Some(r) => r.clone(),
                        None => return false,
                    },
                    Step::NatNonneg(i) => {
                        let mut r = Row::zero(n.max(i + 1));
                        r.a[*i] = 1;
                        r
                    }
                    Step::Combine(terms) => {
                        let mut r = Row::zero(n);
                        for &(k, i) in terms {
                            let Some(s) = ctx.get(i) else { return false };
                            r.c += k * s.c;
                            for (x, y) in r.a.iter_mut().zip(&s.a) {
                                *x += k * y;
                            }
                        }
                        r
                    }
                    Step::Divide(i, d) => {
                        let Some(s) = ctx.get(*i) else { return false };
                        if *d <= 0 || s.a.iter().any(|x| x % d != 0) {
                            return false;
                        }
                        Row {
                            c: s.c.div_euclid(*d),
                            a: s.a.iter().map(|x| x / d).collect(),
                        }
                    }
                };
                ctx.push(row);
                let ok = go(n, input, neg, cases, ctx, rest);
                ctx.pop();
                ok
            }
            Cert::Split(l, left, right) => {
                let mut l = l.clone();
                l.a.resize(n, 0);
                ctx.push(l.clone());
                let ok = go(n, input, neg, cases, ctx, left);
                ctx.pop();
                let other = Row {
                    c: -1 - l.c,
                    a: l.a.iter().map(|x| -x).collect(),
                };
                ctx.push(other);
                let ok2 = go(n, input, neg, cases, ctx, right);
                ctx.pop();
                ok && ok2
            }
            Cert::Cases(f, left, right) => {
                let Some(c) = cases.iter().find(|c| c.fact == *f) else {
                    return false;
                };
                let mark = ctx.len();
                ctx.extend(c.left.iter().cloned());
                let ok = go(n, input, neg, cases, ctx, left);
                ctx.truncate(mark);
                ctx.extend(c.right.iter().cloned());
                let ok2 = go(n, input, neg, cases, ctx, right);
                ctx.truncate(mark);
                ok && ok2
            }
        }
    }
    go(n, &input, &neg, &problem.cases, &mut Vec::new(), cert)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn row(c: i128, a: &[i128]) -> Row {
        Row { c, a: a.to_vec() }
    }

    fn problem(n: usize, facts: &[Row], goal: Option<Row>) -> Problem {
        let mut rows: Vec<(Source, Row)> = facts
            .iter()
            .enumerate()
            .map(|(i, r)| (Source::Input(i), r.clone()))
            .collect();
        if let Some(g) = goal {
            rows.push((Source::NegGoal, g));
        }
        Problem {
            n,
            rows,
            cases: Vec::new(),
        }
    }

    fn proves(p: &Problem) -> bool {
        match refute(p, LIMITS) {
            Ok(cert) => {
                assert!(replay(p, &cert), "the certificate replays: {cert:?}");
                true
            }
            Err(_) => false,
        }
    }

    #[test]
    fn stacked() {
        // x0 <= x1, x1 + 1 <= x2 |- x0 < x2: negation x0 - x2 >= 0.
        let p = problem(
            3,
            &[row(0, &[-1, 1, 0]), row(-1, &[0, -1, 1])],
            Some(row(0, &[1, 0, -1])),
        );
        assert!(proves(&p));
    }

    #[test]
    fn needs_nonnegativity() {
        // |- x <= x + y: negation x - (x + y) - 1 = -y - 1 >= 0.
        let p = problem(2, &[], Some(row(-1, &[0, -1])));
        assert!(proves(&p));
    }

    #[test]
    fn two_x_is_one() {
        let p = problem(1, &[row(1, &[-2]), row(-1, &[2])], None);
        assert!(proves(&p));
    }

    #[test]
    fn disconnected() {
        // y < y |- x < 0
        let p = problem(2, &[row(-1, &[0, 0])], Some(row(0, &[1, 0])));
        assert!(proves(&p));
    }

    #[test]
    fn split_regression() {
        // 1 <= 2x + 3y <= 4, 2y <= 3x + 1, 3x <= 2y + 2
        let p = problem(
            2,
            &[
                row(-1, &[2, 3]),
                row(4, &[-2, -3]),
                row(1, &[3, -2]),
                row(2, &[-3, 2]),
            ],
            None,
        );
        assert!(proves(&p));
    }

    #[test]
    fn integer_model() {
        // x <= y |- x < y fails with x = y.
        let p = problem(2, &[row(0, &[-1, 1])], Some(row(0, &[1, -1])));
        match refute(&p, LIMITS) {
            Err(Failure::Integer(m)) => assert_eq!(m[0], m[1]),
            other => panic!("{other:?}"),
        }
    }

    fn has_cases(cert: &Cert) -> bool {
        match cert {
            Cert::Close(_) => false,
            Cert::Then(_, rest) => has_cases(rest),
            Cert::Split(_, l, r) => has_cases(l) || has_cases(r),
            Cert::Cases(..) => true,
        }
    }

    /// `t = a - b` (atoms t, a, b) as stage 2 quotes it: the rows that always
    /// hold, as facts 0 and 1, and the two cases.
    fn sub_problem(more: &[Row], goal: Option<Row>) -> Problem {
        let mut facts = vec![row(0, &[-1, 1, 0]), row(0, &[1, -1, 1])];
        facts.extend(more.iter().cloned());
        let mut p = problem(3, &facts, goal);
        p.cases.push(Case {
            fact: 0,
            left: vec![
                row(0, &[0, 1, -1]),
                row(0, &[-1, 1, -1]),
                row(0, &[1, -1, 1]),
            ],
            right: vec![
                row(-1, &[0, -1, 1]),
                row(0, &[-1, 0, 0]),
                row(0, &[1, 0, 0]),
            ],
        });
        p
    }

    #[test]
    fn cheap_bound_needs_no_split() {
        // |- a - b <= a: negation t - a - 1 >= 0.
        let p = sub_problem(&[], Some(row(-1, &[1, -1, 0])));
        let cert = refute(&p, LIMITS).expect("proved");
        assert!(replay(&p, &cert));
        assert!(!has_cases(&cert), "{cert:?}");
    }

    #[test]
    fn subtraction_splits_on_demand() {
        // b <= a |- (a - b) + b <= a: negation t + b - a - 1 >= 0.
        let p = sub_problem(&[row(0, &[0, 1, -1])], Some(row(-1, &[1, -1, 1])));
        let cert = refute(&p, LIMITS).expect("proved");
        assert!(replay(&p, &cert));
        assert!(has_cases(&cert), "{cert:?}");
    }

    #[test]
    fn subtraction_without_its_cases_fails() {
        let mut p = sub_problem(&[row(0, &[0, 1, -1])], Some(row(-1, &[1, -1, 1])));
        p.cases.clear();
        assert!(matches!(refute(&p, LIMITS), Err(Failure::Integer(_))));
    }

    #[test]
    fn subtraction_false_goal_fails() {
        // |- (a - b) + b <= a is false at a = 0, b = 1: the cases don't help.
        let p = sub_problem(&[], Some(row(-1, &[1, -1, 1])));
        match refute(&p, LIMITS) {
            Err(Failure::Integer(m)) => assert!(m[1].n < m[2].n, "{m:?}"),
            other => panic!("{other:?}"),
        }
    }

    #[test]
    fn not_equal_splits() {
        // x <= y, x != y |- x < y: negation x - y >= 0.
        let mut p = problem(2, &[row(0, &[-1, 1])], Some(row(0, &[1, -1])));
        p.cases.push(Case {
            fact: 1,
            left: vec![row(-1, &[-1, 1])],
            right: vec![row(-1, &[1, -1])],
        });
        let cert = refute(&p, LIMITS).expect("proved");
        assert!(replay(&p, &cert));
        assert!(matches!(cert, Cert::Cases(1, ..)), "{cert:?}");
    }

    #[test]
    fn replay_refuses_a_missing_case() {
        let p = sub_problem(&[row(0, &[0, 1, -1])], Some(row(-1, &[1, -1, 1])));
        let cert = refute(&p, LIMITS).expect("proved");
        let mut q = sub_problem(&[row(0, &[0, 1, -1])], Some(row(-1, &[1, -1, 1])));
        q.cases[0].fact = 7;
        assert!(!replay(&q, &cert));
    }

    #[test]
    fn budget() {
        let limits = Limits { rows: 3, depth: 6 };
        let p = problem(
            2,
            &[
                row(-1, &[2, 3]),
                row(4, &[-2, -3]),
                row(1, &[3, -2]),
                row(2, &[-3, 2]),
            ],
            None,
        );
        assert_eq!(refute(&p, limits), Err(Failure::Budget));
    }
}

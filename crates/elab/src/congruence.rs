//! Congruence lemmas: `FCong`, beside a definition `F`, says that `F` gives
//! equal results for functions that agree on every argument
//! (`List.sumByCong: ((x: a) -> f1 x = f2 x) -> List.sumBy f1 xs = List.sumBy f2 xs`).
//! No function extensionality is needed. Two passes use them, through this
//! one lookup and validator, so a lemma one accepts the other accepts:
//! `decreasing`'s generated "respects" lemma (`decreasing.rs`) and `rewrite`
//! under a binder (`rewrite.rs`; docs/proposals/proof-automation.md §6.1).

use std::cell::Cell;
use std::rc::Rc;

use stitchwort_core::registry::Builtin;
use stitchwort_core::value::eval;
use stitchwort_core::{DefId, Globals, Icit, Name, Term, Value};

use crate::decreasing::{Binder, map_vars, spine, split_pis};
use crate::{Elaborator, Global, Result};

/// `F`'s congruence lemma, `FCong` beside `F`'s own declaration (not
/// however a call spelled `F`), checked against `F`. `Decidable.elim` and
/// `Bool.ifThenElse` have theirs in the prelude.
pub(crate) fn lookup(e: &Elaborator, f: DefId) -> Result<Lookup> {
    let g = &e.globals;
    let name = g.def(f).name.to_string();
    let lemma_name = format!("{name}Cong");
    let r = &g.registry;
    let lemma = if Some(f) == r.def(Builtin::ElimDec) {
        r.def(Builtin::ElimDecCong)
    } else if Some(f) == r.def(Builtin::IfThenElse) {
        r.def(Builtin::IfCong)
    } else {
        [format!("Std.{name}"), name.clone()]
            .into_iter()
            .find(|k| matches!(e.scope.get(k), Some((Global::Def(id), _)) if id == f))
            .and_then(|k| match e.scope.get(&format!("{k}Cong")) {
                Some((Global::Def(id), _)) => Some(id),
                _ => None,
            })
    };
    Ok(match lemma {
        None => Lookup::Missing(lemma_name),
        Some(lemma) => match validate_cong(g, f, lemma)? {
            Ok(desc) => Lookup::Found(Rc::new(desc)),
            Err(why) => Lookup::Bad(lemma_name, why),
        },
    })
}

/// What a congruence lemma `FCong` says, in terms of `F`'s parameters:
/// `F`'s parameters in order, each callback `c` twice (`c1`, `c2`), then
/// for each callback `(x…) -> c1 x… = c2 x…`, proving `F …c1… = F …c2…`.
pub(crate) struct CongDesc {
    pub(crate) lemma: DefId,
    /// How many parameters `F` has, besides its effect-row parameters.
    pub(crate) params: usize,
    /// Where `F`'s effect-row parameters are among all its parameters: a
    /// call the lemma rewrites passes the empty row for each.
    pub(crate) rows: Vec<usize>,
    /// Which of them are callbacks, in order.
    pub(crate) callbacks: Vec<usize>,
    /// For each of `F`'s parameters, whether a later parameter's type or
    /// the result's mentions it (so it can't be rewritten on its own).
    pub(crate) dependent: Vec<bool>,
    /// The lemma's parameters.
    pub(crate) tel: Vec<Binder>,
    /// Each premise's binders: where its equation is.
    pub(crate) premises: Vec<Vec<Binder>>,
}

impl CongDesc {
    /// The level of callback `m`'s first copy among the lemma's parameters.
    pub(crate) fn callback_level(&self, m: usize) -> usize {
        self.callbacks[m] + m
    }
}

#[derive(Clone)]
pub(crate) enum Lookup {
    /// No lemma by that name.
    Missing(String),
    /// A lemma whose statement isn't a congruence lemma for `F`: why.
    Bad(String, String),
    Found(Rc<CongDesc>),
}

/// `F`'s telescope and result with its effect-row parameters (implicit, of
/// type `Effects`) replaced by the empty row and left out, and where they
/// were.
fn at_empty_row(
    g: &Globals,
    tel: Vec<Binder>,
    res: Term,
) -> Result<(Vec<Binder>, Term, Vec<usize>)> {
    let (Some(row_data), Some((empty_data, empty_ctor))) = (
        g.registry.data(Builtin::Row),
        g.registry.ctor(Builtin::RowEmpty),
    ) else {
        return Ok((tel, res, Vec::new()));
    };
    let rows: Vec<usize> = (tel.iter().enumerate())
        .filter(|(_, b)| {
            b.icit.is_implicit()
                && matches!(b.ty.strip_loc(), Term::Data(d, args) if *d == row_data && args.is_empty())
        })
        .map(|(i, _)| i)
        .collect();
    if rows.is_empty() {
        return Ok((tel, res, rows));
    }
    let empty = Term::Ctor(empty_data, empty_ctor, Vec::new());
    // A term written under the first `j` of the old binders, moved under the
    // binders kept among them.
    let moved = |t: &Term, j: usize| -> Result<Term> {
        let kept_before = |level: usize| (0..level).filter(|l| !rows.contains(l)).count();
        let new_depth = kept_before(j);
        map_vars(g, t, 0, &|ix, d| {
            if ix < d {
                return Ok(Term::Var(ix));
            }
            let level = j - 1 - (ix - d);
            if rows.contains(&level) {
                return Ok(empty.clone());
            }
            Ok(Term::Var(new_depth - 1 - kept_before(level) + d))
        })
    };
    let mut kept = Vec::new();
    for (j, b) in tel.iter().enumerate() {
        if rows.contains(&j) {
            continue;
        }
        kept.push(Binder {
            name: b.name.clone(),
            icit: b.icit,
            ty: moved(&b.ty, j)?,
        });
    }
    let res = moved(&res, tel.len())?;
    Ok((kept, res, rows))
}

/// `args` without those at `rows`, each of which must be the empty row;
/// `None` if one isn't.
pub(crate) fn without_rows<T: Clone + std::borrow::Borrow<Term>>(
    g: &Globals,
    args: &[(T, Icit)],
    rows: &[usize],
) -> Option<Vec<(T, Icit)>> {
    let empty = g.registry.ctor(Builtin::RowEmpty);
    let mut kept = Vec::new();
    for (i, (a, icit)) in args.iter().enumerate() {
        if rows.contains(&i) {
            let is_empty = matches!(a.borrow().strip_loc(), Term::Ctor(d, c, fields)
                if fields.is_empty() && empty == Some((*d, *c)));
            if !is_empty {
                return None;
            }
            continue;
        }
        kept.push((a.clone(), *icit));
    }
    Some(kept)
}

/// Checks that `lemma`'s statement is a congruence lemma for `f` (3a.4 step
/// 2), and describes it; or says what's wrong with it.
pub(crate) fn validate_cong(
    g: &Globals,
    f: DefId,
    lemma: DefId,
) -> Result<std::result::Result<CongDesc, String>> {
    let f_name = g.def(f).name.to_string();
    let (ftel, fres) = split_pis(&g.def(f).ty, None);
    // `F`'s effect-row parameters are the empty row's in a congruence lemma,
    // which is about `F`'s pure use (`List.map`'s `e`).
    let (ftel, fres, rows) = at_empty_row(g, ftel, fres)?;
    let (ltel, lres) = split_pis(&g.def(lemma).ty, None);
    let n = ftel.len();
    let total = ltel.len();
    if total <= n || (total - n) % 2 != 0 {
        return Ok(Err(format!(
            "it should take `{f_name}`'s {n} parameters, each function compared given twice, \
             then one premise for each; it takes {total}"
        )));
    }
    let k = (total - n) / 2;
    let params = n + k;
    // A premise among the parameters: the commonest mistake, named as such.
    if let Some(b) = ltel[..params]
        .iter()
        .find(|b| matches!(split_pis(&b.ty, None).1.strip_loc(), Term::Eq(..)))
    {
        return Ok(Err(format!(
            "its premise `{}` comes before the end of `{f_name}`'s parameters; the premises \
             go after all of them",
            b.name
        )));
    }
    // The premises: which parameters each compares.
    let mut firsts = Vec::new();
    let mut premises = Vec::new();
    for m in 0..k {
        let level = params + m;
        let (xs, body) = split_pis(&ltel[level].ty, None);
        let depth = level + xs.len();
        let wrong = || {
            format!(
                "its premise {} isn't `(x…) -> f1 x… = f2 x…` for the two copies of a \
                 parameter",
                m + 1
            )
        };
        let Term::Eq(_, lhs, rhs) = body.strip_loc() else {
            return Ok(Err(wrong()));
        };
        let applied = |t: &Term| -> Option<usize> {
            let (head, args) = spine(t);
            let Term::Var(ix) = head else { return None };
            if *ix >= depth || args.len() != xs.len() {
                return None;
            }
            for (j, (a, icit)) in args.iter().enumerate() {
                if !matches!(a.strip_loc(), Term::Var(v) if *v == xs.len() - 1 - j)
                    || *icit != xs[j].icit
                {
                    return None;
                }
            }
            Some(depth - 1 - ix)
        };
        let (Some(c1), Some(c2)) = (applied(lhs), applied(rhs)) else {
            return Ok(Err(wrong()));
        };
        if c2 != c1 + 1 || c2 >= params || firsts.last().is_some_and(|&l| l + 1 >= c1) {
            return Ok(Err(wrong()));
        }
        firsts.push(c1);
        premises.push(xs);
    }
    // The parameters: `F`'s, with the callbacks twice.
    let mut f_of = Vec::new(); // lemma level -> F's parameter
    let mut second = Vec::new(); // whether it's a callback's second copy
    let mut first_level = Vec::new(); // F's parameter -> lemma level
    let mut callbacks = Vec::new();
    let mut j = 0;
    while j < params {
        let i = first_level.len();
        first_level.push(j);
        f_of.push(i);
        second.push(false);
        if firsts.contains(&j) {
            callbacks.push(i);
            f_of.push(i);
            second.push(true);
            j += 2;
        } else {
            j += 1;
        }
    }
    if first_level.len() != n {
        return Ok(Err(format!(
            "it should take `{f_name}`'s {n} parameters before its premises, each function \
             compared given twice"
        )));
    }
    let is_first_copy = |l: usize| firsts.contains(&l);
    for j in 0..params {
        let i = f_of[j];
        let what = || {
            let name = &ltel[j].name;
            format!(
                "its parameter `{name}` should be `{f_name}`'s parameter `{}`, at the same type{}",
                ftel[i].name,
                if second[j] {
                    " as the copy before it"
                } else {
                    ""
                }
            )
        };
        if ltel[j].icit != ftel[i].icit {
            return Ok(Err(what()));
        }
        // The lemma's type, moved to `F`'s context: it may not mention a
        // callback.
        let bad = Cell::new(false);
        let moved = map_vars(g, &ltel[j].ty, 0, &|ix, d| {
            if ix < d {
                return Ok(Term::Var(ix));
            }
            let level = j - 1 - (ix - d);
            if second[level] || is_first_copy(level) {
                bad.set(true);
                return Ok(Term::Var(ix));
            }
            Ok(Term::Var(i - 1 - f_of[level] + d))
        })?;
        if bad.get() {
            return Ok(Err(format!(
                "its parameter `{}`'s type mentions a function it compares",
                ltel[j].name
            )));
        }
        let env: Vec<Value> = (0..i).map(Value::var).collect();
        let a = eval(g, &env, &moved)?;
        let b = eval(g, &env, &ftel[i].ty)?;
        if !stitchwort_core::value::conv(g, i, &a, &b)? {
            return Ok(Err(what()));
        }
    }
    // The result: `F …c1… = F …c2…`, the other arguments the same.
    let result_ok = (|| {
        let Term::Eq(_, lhs, rhs) = lres.strip_loc() else {
            return false;
        };
        let side = |t: &Term, copy: usize| {
            let (head, args) = spine(t);
            if !matches!(head, Term::Def(d) if *d == f) {
                return false;
            }
            let Some(args) = without_rows(g, &args, &rows) else {
                return false;
            };
            if args.len() != n {
                return false;
            }
            args.iter().enumerate().all(|(i, (a, icit))| {
                let level = first_level[i] + if callbacks.contains(&i) { copy } else { 0 };
                *icit == ftel[i].icit
                    && matches!(a.strip_loc(), Term::Var(v) if *v == total - 1 - level)
            })
        };
        side(lhs, 0) && side(rhs, 1)
    })();
    if !result_ok {
        return Ok(Err(format!(
            "its result should be `{f_name} … f1 … = {f_name} … f2 …`, with its parameters \
             in order and the copies of each function on either side"
        )));
    }
    // `F`'s own parameters a later type depends on.
    let dependent = (0..n)
        .map(|i| (i + 1..n).any(|l| ftel[l].ty.mentions(l - 1 - i)) || fres.mentions(n - 1 - i))
        .collect::<Vec<_>>();
    if let Some(&i) = callbacks.iter().find(|&&i| dependent[i]) {
        return Ok(Err(format!(
            "`{f_name}`'s later parameters or result depend on `{}`, which `decreasing` \
             doesn't support",
            ftel[i].name
        )));
    }
    Ok(Ok(CongDesc {
        lemma,
        params: n,
        rows,
        callbacks,
        dependent,
        tel: ltel,
        premises,
    }))
}

/// A statement of the congruence lemma `F` would need, for messages:
/// `theorem FCong (f1: a -> b) (f2: a -> b) (xs: List a) (ef: (x: a) -> f1 x = f2 x): F f1 xs = F f2 xs`.
/// Type parameters and effect rows are left to be bound automatically.
pub(crate) fn sketch(g: &Globals, f: DefId) -> String {
    let name = g.def(f).name.to_string();
    let (tel, _) = split_pis(&g.def(f).ty, None);
    let row = g.registry.data(Builtin::Row);
    let print = |names: &[Name], t: &Term| stitchwort_core::pretty::term(g, names, t);
    let mut names: Vec<Name> = Vec::new();
    let mut params = String::new();
    let mut premises = String::new();
    let (mut left, mut right) = (String::new(), String::new());
    for b in &tel {
        let ty = print(&names, &b.ty);
        let x: Name = match b.name.as_ref() {
            "_" | "" => format!("arg{}", names.len() + 1).as_str().into(),
            _ => b.name.clone(),
        };
        match b.icit {
            Icit::Implicit => {
                let bound = matches!(b.ty.strip_loc(), Term::Sort(_))
                    || matches!(b.ty.strip_loc(), Term::Data(d, _) if Some(*d) == row);
                if !bound {
                    params.push_str(&format!(" [{x}: {ty}]"));
                }
            }
            Icit::Auto => params.push_str(&format!(" [auto {x}: {ty}]")),
            Icit::Explicit => match b.ty.strip_loc() {
                Term::Pi(..) => {
                    params.push_str(&format!(" ({x}1: {ty}) ({x}2: {ty})"));
                    left.push_str(&format!(" {x}1"));
                    right.push_str(&format!(" {x}2"));
                    // `(y: a) -> (z: b) -> f1 y z = f2 y z`
                    let mut inner = names.clone();
                    let mut binders = String::new();
                    let mut args = String::new();
                    let mut t = b.ty.strip_loc();
                    let fresh = ["x", "y", "z", "w"];
                    while let Term::Pi(y, _, dom, cod) = t {
                        let y: String = match y.as_ref() {
                            "_" | "" => fresh
                                .get(inner.len() - names.len())
                                .unwrap_or(&"v")
                                .to_string(),
                            y => y.to_string(),
                        };
                        binders.push_str(&format!("({y}: {}) -> ", print(&inner, dom)));
                        args.push_str(&format!(" {y}"));
                        inner.push(y.as_str().into());
                        t = cod.strip_loc();
                    }
                    premises.push_str(&format!(" (e{x}: {binders}{x}1{args} = {x}2{args})"));
                }
                _ => {
                    params.push_str(&format!(" ({x}: {ty})"));
                    left.push_str(&format!(" {x}"));
                    right.push_str(&format!(" {x}"));
                }
            },
        }
        names.push(x);
    }
    format!("theorem {name}Cong{params}{premises}: {name}{left} = {name}{right}")
}

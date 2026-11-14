//! Where two versions of a declaration first differ outside proof positions
//! (SW-2728): the walk behind the trial's "it would change what `f` means"
//! when a definition's term changed under the proofs-only promise.
//!
//! It compares the same parts, in the same order, as `hash.rs`'s
//! [`Mode::Proofless`](stitchwort_core::hash), so a difference it finds is
//! exactly a difference the proofless hash covers. It skips the parts that
//! hash leaves out: a call of a definition whose result is a proof,
//! `Quot.ind` and `Quot.sound`, an argument at a parameter or a field whose
//! type is a proposition, `J`'s proof, and `Quot.lift`'s respects-proof.
//! Locals' names and source locations are ignored, as they are hashed
//! without them; bound variables are printed as the old declaration named
//! them. The old terms keep the old environment's ids, which an edit that
//! adds or removes a declaration shifts: they're translated to the
//! re-checked environment's ids by full name first. A name with no
//! declaration now is the difference's place.

use std::collections::BTreeMap;
use std::rc::Rc;

use stitchwort_core::erase::proof_positions;
use stitchwort_core::pretty;
use stitchwort_core::term::{Branch, Icit, Name, NumArm, QuotForm, Term};
use stitchwort_core::value::{proof_field, proof_param};
use stitchwort_core::{DataId, DefId, Ev};
use stitchwort_elab::shown::cut_to;

/// The longest each side of a difference is shown.
const SHOWN: usize = 80;

/// The full names of the definitions and data types an old declaration's
/// terms mention, by their ids then.
#[derive(Clone, Default)]
pub(crate) struct RefNames {
    defs: BTreeMap<usize, String>,
    datas: BTreeMap<usize, String>,
}

/// A definition's type and body as they were before an edit, whether its
/// result is a proof (which the proofless hash leaves its body out of), and
/// the names its ids had then. Kept because the trial's rewind forgets the
/// old declarations, and the re-check can give the same names new ids.
#[derive(Clone)]
pub(crate) struct DeclTerms {
    pub(crate) ty: Rc<Term>,
    pub(crate) body: Option<Rc<Term>>,
    pub(crate) proof_result: bool,
    pub(crate) names: RefNames,
}

/// The full names of every definition and data type an old declaration's
/// terms mention. Constructors are (data type, index), so a data type's
/// name is enough.
pub(crate) fn ref_names(g: &Ev, ty: &Term, body: Option<&Term>) -> RefNames {
    let mut names = RefNames::default();
    for term in std::iter::once(ty).chain(body) {
        for (term, _) in term.subterms() {
            match term {
                Term::Def(id) => {
                    names.defs.entry(id.0).or_insert_with(|| {
                        g.env
                            .defs()
                            .get(id.0)
                            .map(|def| def.path().to_string())
                            .unwrap_or_else(|| format!("#{}", id.0))
                    });
                }
                Term::Data(id, _)
                | Term::Ctor(id, _, _)
                | Term::Case(_, id, _)
                | Term::Proj(id, _, _) => {
                    names.datas.entry(id.0).or_insert_with(|| {
                        g.env
                            .datas()
                            .get(id.0)
                            .map(|data| data.path().to_string())
                            .unwrap_or_else(|| format!("#{}", id.0))
                    });
                }
                _ => {}
            }
        }
    }
    names
}

/// The ids the re-checked environment gives declarations, by full name.
#[derive(Default)]
pub(crate) struct NewIds {
    defs: BTreeMap<String, usize>,
    datas: BTreeMap<String, usize>,
}

impl NewIds {
    pub(crate) fn of(g: &Ev) -> Self {
        NewIds {
            defs: g
                .env
                .defs()
                .iter()
                .enumerate()
                .map(|(i, def)| (def.path().to_string(), i))
                .collect(),
            datas: g
                .env
                .datas()
                .iter()
                .enumerate()
                .map(|(i, data)| (data.path().to_string(), i))
                .collect(),
        }
    }
}

/// The first place two terms differ outside proof positions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Difference {
    /// Where, in short: `body` or `type`, then the path into it
    /// (`body, argument 2 of the call to List.map`).
    pub at: String,
    /// The old part there, as printed, cut to about [`SHOWN`] characters.
    pub old: String,
    /// The new part there.
    pub new: String,
}

/// The first difference in a declaration's type, or failing that its body.
/// `None` if they agree outside proof positions.
///
/// The old terms have the old environment's ids; they're translated to the
/// re-checked environment's ids by full name first, since an edit that adds
/// or removes a declaration shifts the ids after it. If a name has no
/// counterpart now, the difference is at its first mention.
pub(crate) fn declaration(
    g: &Ev,
    old: &DeclTerms,
    old_body: Option<&Term>,
    new_ty: &Term,
    new_body: Option<&Term>,
    ids: &NewIds,
) -> Option<Difference> {
    let old_ty = match translate(g, &old.ty, &old.names, ids, &mut Vec::new()) {
        Ok(term) => term,
        Err(TranslateError::Missing { name, path }) => {
            return Some(missing_difference("type", name, path));
        }
        Err(TranslateError::TooDeep) => return None,
    };
    if let Some(found) = compare(g, &old_ty, new_ty) {
        return Some(found.difference(g, "type"));
    }
    match (old_body, new_body) {
        (Some(old_body), Some(new_body)) => {
            let old_body = match translate(g, old_body, &old.names, ids, &mut Vec::new()) {
                Ok(term) => term,
                Err(TranslateError::Missing { name, path }) => {
                    return Some(missing_difference("body", name, path));
                }
                Err(TranslateError::TooDeep) => return None,
            };
            compare(g, &old_body, new_body).map(|found| found.difference(g, "body"))
        }
        (None, None) => None,
        _ => {
            let old = match old_body {
                Some(term) => match translate(g, term, &old.names, ids, &mut Vec::new()) {
                    Ok(term) => show(g, &[], &term),
                    Err(TranslateError::Missing { name, path }) => {
                        return Some(missing_difference("body", name, path));
                    }
                    Err(TranslateError::TooDeep) => return None,
                },
                None => "(no body)".to_string(),
            };
            Some(Difference {
                at: "body".to_string(),
                old,
                new: new_body.map_or_else(|| "(no body)".to_string(), |t| show(g, &[], t)),
            })
        }
    }
}

/// A difference where an old name has no declaration now.
fn missing_difference(prefix: &str, name: String, path: Vec<String>) -> Difference {
    let at = if path.is_empty() {
        prefix.to_string()
    } else {
        format!("{prefix}, {}", path.join(", "))
    };
    Difference {
        at,
        old: name,
        new: "(not in the edited project)".to_string(),
    }
}

enum TranslateError {
    Missing { name: String, path: Vec<String> },
    TooDeep,
}

/// `id` in the re-checked environment, by the full name it had.
fn translate_def(
    names: &RefNames,
    ids: &NewIds,
    id: DefId,
    path: &[String],
) -> Result<DefId, TranslateError> {
    let name = names
        .defs
        .get(&id.0)
        .cloned()
        .unwrap_or_else(|| format!("#{}", id.0));
    match ids.defs.get(&name) {
        Some(&id) => Ok(DefId(id)),
        None => Err(TranslateError::Missing {
            name,
            path: path.to_vec(),
        }),
    }
}

/// [`translate_def`] for a data type.
fn translate_data(
    names: &RefNames,
    ids: &NewIds,
    id: DataId,
    path: &[String],
) -> Result<DataId, TranslateError> {
    let name = names
        .datas
        .get(&id.0)
        .cloned()
        .unwrap_or_else(|| format!("#{}", id.0));
    match ids.datas.get(&name) {
        Some(&id) => Ok(DataId(id)),
        None => Err(TranslateError::Missing {
            name,
            path: path.to_vec(),
        }),
    }
}

/// The old term with the re-checked environment's ids. Its source locations
/// are dropped, as the hash ignores them.
fn translate(
    g: &Ev,
    term: &Term,
    names: &RefNames,
    ids: &NewIds,
    path: &mut Vec<String>,
) -> Result<Term, TranslateError> {
    if g.machine.budget.stack_exhausted() {
        return Err(TranslateError::TooDeep);
    }
    let term = term.strip_loc();
    Ok(match term {
        Term::Loc(_, inner) => translate(g, inner, names, ids, path)?,
        Term::Var(i) => Term::Var(*i),
        Term::Def(id) => Term::Def(translate_def(names, ids, *id, path)?),
        Term::Data(d, args) => {
            let d = translate_data(names, ids, *d, path)?;
            let name = data_name(g, d);
            let mut out = Vec::with_capacity(args.len());
            for (k, arg) in args.iter().enumerate() {
                path.push(format!("argument {} of {}", k + 1, name));
                out.push(Rc::new(translate(g, arg, names, ids, path)?));
                path.pop();
            }
            Term::Data(d, out)
        }
        Term::Ctor(d, c, fields) => {
            let d = translate_data(names, ids, *d, path)?;
            let name = ctor_name(g, d, *c);
            let mut out = Vec::with_capacity(fields.len());
            for (i, field) in fields.iter().enumerate() {
                path.push(format!("field {} of {}", i + 1, name));
                out.push(Rc::new(translate(g, field, names, ids, path)?));
                path.pop();
            }
            Term::Ctor(d, *c, out)
        }
        Term::Nat(n) => Term::Nat(n.clone()),
        Term::Chars(chars) => Term::Chars(chars.clone()),
        Term::Sort(sort) => Term::Sort(*sort),
        Term::Pi(name, icit, a, b) => {
            path.push("the domain of the function type".to_string());
            let a = translate(g, a, names, ids, path)?;
            path.pop();
            path.push("under the binder, the body of the function type".to_string());
            let b = translate(g, b, names, ids, path)?;
            path.pop();
            Term::Pi(name.clone(), *icit, Rc::new(a), Rc::new(b))
        }
        Term::Lam(name, icit, body) => {
            path.push("under the binder, the body".to_string());
            let body = translate(g, body, names, ids, path)?;
            path.pop();
            Term::Lam(name.clone(), *icit, Rc::new(body))
        }
        Term::App(..) => {
            let (head, args) = full_spine(term);
            let mut out = translate(g, head, names, ids, path)?;
            let name = call_name(g, &out);
            for (k, (arg, icit)) in args.into_iter().enumerate() {
                path.push(format!("argument {} of the call to {name}", k + 1));
                let arg = translate(g, arg, names, ids, path)?;
                path.pop();
                out = Term::App(Rc::new(out), Rc::new(arg), icit);
            }
            out
        }
        Term::Ann(a, b) => {
            path.push("the term".to_string());
            let a = translate(g, a, names, ids, path)?;
            path.pop();
            path.push("its type annotation".to_string());
            let b = translate(g, b, names, ids, path)?;
            path.pop();
            Term::Ann(Rc::new(a), Rc::new(b))
        }
        Term::Let(name, a, v, b, erased) => {
            path.push("the type of the let".to_string());
            let a = translate(g, a, names, ids, path)?;
            path.pop();
            path.push("the value of the let".to_string());
            let v = translate(g, v, names, ids, path)?;
            path.pop();
            path.push("under the binder, the body of the let".to_string());
            let b = translate(g, b, names, ids, path)?;
            path.pop();
            Term::Let(name.clone(), Rc::new(a), Rc::new(v), Rc::new(b), *erased)
        }
        Term::Case(ix, d, branches) => {
            let d = translate_data(names, ids, *d, path)?;
            let mut out = Vec::with_capacity(branches.len());
            for (i, branch) in branches.iter().enumerate() {
                let body = match &branch.body {
                    Some(body) => {
                        let segment = format!("in the branch for {}", ctor_name(g, d, i));
                        path.push(segment);
                        let body = translate(g, body, names, ids, path)?;
                        path.pop();
                        Some(Rc::new(body))
                    }
                    None => None,
                };
                out.push(Branch {
                    names: branch.names.clone(),
                    body,
                });
            }
            Term::Case(*ix, d, out.into())
        }
        Term::NumCase(ix, arms, default) => {
            let mut out = Vec::with_capacity(arms.len());
            for arm in arms.iter() {
                path.push(format!("the arm for {}", arm.value));
                let body = translate(g, &arm.body, names, ids, path)?;
                path.pop();
                out.push(NumArm {
                    value: arm.value.clone(),
                    body: Rc::new(body),
                });
            }
            path.push("the default".to_string());
            let default = translate(g, default, names, ids, path)?;
            path.pop();
            Term::NumCase(*ix, out.into(), Rc::new(default))
        }
        Term::Eq(ty, a, b) => {
            let ty = match ty {
                Some(ty) => {
                    path.push("the type of the equality".to_string());
                    let ty = translate(g, ty, names, ids, path)?;
                    path.pop();
                    Some(Rc::new(ty))
                }
                None => None,
            };
            path.push("the left side".to_string());
            let a = translate(g, a, names, ids, path)?;
            path.pop();
            path.push("the right side".to_string());
            let b = translate(g, b, names, ids, path)?;
            path.pop();
            Term::Eq(ty, Rc::new(a), Rc::new(b))
        }
        Term::Refl => Term::Refl,
        Term::J(motive, base, proof) => {
            path.push("the motive of J".to_string());
            let motive = translate(g, motive, names, ids, path)?;
            path.pop();
            path.push("the base of J".to_string());
            let base = translate(g, base, names, ids, path)?;
            path.pop();
            path.push("the proof of J".to_string());
            let proof = translate(g, proof, names, ids, path)?;
            path.pop();
            Term::J(Rc::new(motive), Rc::new(base), Rc::new(proof))
        }
        Term::Proj(d, i, t) => {
            let d = translate_data(names, ids, *d, path)?;
            path.push("the projected value".to_string());
            let t = translate(g, t, names, ids, path)?;
            path.pop();
            Term::Proj(d, *i, Rc::new(t))
        }
        Term::Quot(form, args, erased) => {
            let name = quot_name(*form);
            let mut out = Vec::with_capacity(args.len());
            for (k, arg) in args.iter().enumerate() {
                path.push(format!("argument {} of {}", k + 1, name));
                out.push(Rc::new(translate(g, arg, names, ids, path)?));
                path.pop();
            }
            Term::Quot(*form, out, *erased)
        }
        Term::Meta(i) => Term::Meta(*i),
    })
}

fn compare<'t>(g: &Ev, old: &'t Term, new: &'t Term) -> Option<Found<'t>> {
    walk(g, old, new, &mut Vec::new(), &mut Vec::new())
}

/// A differing pair, with where it is and the binders in scope there.
struct Found<'t> {
    old: &'t Term,
    new: &'t Term,
    names: Vec<Name>,
    path: Vec<String>,
}

impl<'t> Found<'t> {
    fn here(old: &'t Term, new: &'t Term, names: &[Name], path: &[String]) -> Self {
        Found {
            old,
            new,
            names: names.to_vec(),
            path: path.to_vec(),
        }
    }

    fn difference(self, g: &Ev, prefix: &str) -> Difference {
        let at = if self.path.is_empty() {
            prefix.to_string()
        } else {
            format!("{prefix}, {}", self.path.join(", "))
        };
        Difference {
            at,
            old: show(g, &self.names, self.old),
            new: show(g, &self.names, self.new),
        }
    }
}

/// [`walk`] one step in, with `segment` added to the path.
fn step<'t>(
    g: &Ev,
    old: &'t Term,
    new: &'t Term,
    names: &mut Vec<Name>,
    path: &mut Vec<String>,
    segment: String,
) -> Option<Found<'t>> {
    path.push(segment);
    let found = walk(g, old, new, names, path);
    path.pop();
    found
}

/// [`step`] under a binder, whose name is the old declaration's (names
/// aren't hashed).
fn under<'t>(
    g: &Ev,
    old: &'t Term,
    new: &'t Term,
    names: &mut Vec<Name>,
    path: &mut Vec<String>,
    binder: &Name,
    segment: String,
) -> Option<Found<'t>> {
    names.push(binder.clone());
    let found = step(g, old, new, names, path, segment);
    names.pop();
    found
}

/// The first difference between `old` and `new`, in the order the proofless
/// hash walks them.
fn walk<'t>(
    g: &Ev,
    old: &'t Term,
    new: &'t Term,
    names: &mut Vec<Name>,
    path: &mut Vec<String>,
) -> Option<Found<'t>> {
    if g.machine.budget.stack_exhausted() {
        return None;
    }
    let old = old.strip_loc();
    let new = new.strip_loc();
    // The hash writes a proof as one marker before looking at any of it.
    let (old_proof, new_proof) = (is_proof(g, old), is_proof(g, new));
    if old_proof || new_proof {
        return (old_proof != new_proof).then(|| Found::here(old, new, names, path));
    }
    match (old, new) {
        (Term::Var(i), Term::Var(j)) => (i != j).then(|| Found::here(old, new, names, path)),
        (Term::Def(i), Term::Def(j)) => (i != j).then(|| Found::here(old, new, names, path)),
        (Term::Data(d, xs), Term::Data(e, ys)) if d == e && xs.len() == ys.len() => {
            let name = data_name(g, *d);
            for (k, (x, y)) in xs.iter().zip(ys.iter()).enumerate() {
                let old_marker = proof_param(g, *d, k) || is_proof(g, x);
                let new_marker = proof_param(g, *d, k) || is_proof(g, y);
                if old_marker && new_marker {
                    continue;
                }
                let segment = format!("argument {} of {}", k + 1, name);
                if let Some(found) = step(g, x, y, names, path, segment) {
                    return Some(found);
                }
            }
            None
        }
        (Term::Ctor(d, c, xs), Term::Ctor(e, k, ys))
            if d == e && c == k && xs.len() == ys.len() =>
        {
            let name = ctor_name(g, *d, *c);
            for (i, (x, y)) in xs.iter().zip(ys.iter()).enumerate() {
                let old_marker = proof_field(g, *d, *c, i) || is_proof(g, x);
                let new_marker = proof_field(g, *d, *c, i) || is_proof(g, y);
                if old_marker && new_marker {
                    continue;
                }
                let segment = format!("field {} of {}", i + 1, name);
                if let Some(found) = step(g, x, y, names, path, segment) {
                    return Some(found);
                }
            }
            None
        }
        (Term::Nat(i), Term::Nat(j)) => (i != j).then(|| Found::here(old, new, names, path)),
        (Term::Chars(i), Term::Chars(j)) => {
            (i.as_slice() != j.as_slice()).then(|| Found::here(old, new, names, path))
        }
        (Term::Sort(i), Term::Sort(j)) => (i != j).then(|| Found::here(old, new, names, path)),
        (Term::Pi(x, i, a, b), Term::Pi(_, j, c, d)) if i == j => {
            let segment = "the domain of the function type".to_string();
            if let Some(found) = step(g, a, c, names, path, segment) {
                return Some(found);
            }
            under(
                g,
                b,
                d,
                names,
                path,
                x,
                "under the binder, the body of the function type".to_string(),
            )
        }
        (Term::Lam(x, i, b), Term::Lam(_, j, d)) if i == j => under(
            g,
            b,
            d,
            names,
            path,
            x,
            "under the binder, the body".to_string(),
        ),
        (Term::App(..), Term::App(..)) => {
            let name = call_name(g, old);
            let (old_head, old_args) = full_spine(old);
            let (new_head, new_args) = full_spine(new);
            let segment = format!("the head of the call to {name}");
            if let Some(found) = step(g, old_head, new_head, names, path, segment) {
                return Some(found);
            }
            if old_args.len() != new_args.len() {
                return Some(Found::here(old, new, names, path));
            }
            for (k, ((x, xi), (y, yi))) in old_args.iter().zip(&new_args).enumerate() {
                if xi != yi {
                    return Some(Found::here(old, new, names, path));
                }
                let old_marker = proof_parameter(g, old_head, k + 1) || is_proof(g, x);
                let new_marker = proof_parameter(g, new_head, k + 1) || is_proof(g, y);
                if old_marker && new_marker {
                    continue;
                }
                let segment = format!("argument {} of the call to {name}", k + 1);
                if let Some(found) = step(g, x, y, names, path, segment) {
                    return Some(found);
                }
            }
            None
        }
        (Term::Ann(a, b), Term::Ann(c, d)) => {
            if let Some(found) = step(g, a, c, names, path, "the term".to_string()) {
                return Some(found);
            }
            step(g, b, d, names, path, "its type annotation".to_string())
        }
        (Term::Let(x, a, v, b, _), Term::Let(_, c, w, d, _)) => {
            if let Some(found) = step(g, a, c, names, path, "the type of the let".to_string()) {
                return Some(found);
            }
            if let Some(found) = step(g, v, w, names, path, "the value of the let".to_string()) {
                return Some(found);
            }
            under(
                g,
                b,
                d,
                names,
                path,
                x,
                "under the binder, the body of the let".to_string(),
            )
        }
        (Term::Case(ix, d, xs), Term::Case(iy, e, ys))
            if ix == iy && d == e && xs.len() == ys.len() =>
        {
            for (i, (x, y)) in xs.iter().zip(ys.iter()).enumerate() {
                if x.names.len() != y.names.len() {
                    return Some(Found::here(old, new, names, path));
                }
                match (&x.body, &y.body) {
                    (None, None) => {}
                    (Some(s), Some(t)) => {
                        let segment = format!("in the branch for {}", ctor_name(g, *d, i));
                        names.extend(x.names.iter().cloned());
                        path.push(segment);
                        let found = walk(g, s, t, names, path);
                        path.pop();
                        names.truncate(names.len() - x.names.len());
                        if found.is_some() {
                            return found;
                        }
                    }
                    _ => return Some(Found::here(old, new, names, path)),
                }
            }
            None
        }
        (Term::NumCase(ix, xs, s), Term::NumCase(iy, ys, t))
            if ix == iy && xs.len() == ys.len() =>
        {
            for (x, y) in xs.iter().zip(ys.iter()) {
                if x.value != y.value {
                    return Some(Found::here(old, new, names, path));
                }
                let segment = format!("the arm for {}", x.value);
                if let Some(found) = step(g, &x.body, &y.body, names, path, segment) {
                    return Some(found);
                }
            }
            step(g, s, t, names, path, "the default".to_string())
        }
        (Term::Eq(ta, a, b), Term::Eq(tc, c, d)) => {
            match (ta, tc) {
                (Some(x), Some(y)) => {
                    if let Some(found) =
                        step(g, x, y, names, path, "the type of the equality".to_string())
                    {
                        return Some(found);
                    }
                }
                (None, None) => {}
                _ => return Some(Found::here(old, new, names, path)),
            }
            if let Some(found) = step(g, a, c, names, path, "the left side".to_string()) {
                return Some(found);
            }
            step(g, b, d, names, path, "the right side".to_string())
        }
        (Term::Refl, Term::Refl) => None,
        (Term::J(m, b, _), Term::J(n, c, _)) => {
            if let Some(found) = step(g, m, n, names, path, "the motive of J".to_string()) {
                return Some(found);
            }
            step(g, b, c, names, path, "the base of J".to_string())
        }
        (Term::Proj(d, i, x), Term::Proj(e, j, y)) if d == e && i == j => {
            step(g, x, y, names, path, "the projected value".to_string())
        }
        (Term::Quot(f, xs, _), Term::Quot(h, ys, _)) if f == h && xs.len() == ys.len() => {
            for (k, (x, y)) in xs.iter().zip(ys.iter()).enumerate() {
                if *f == QuotForm::Lift && k == 4 {
                    continue;
                }
                let old_marker = is_proof(g, x);
                let new_marker = is_proof(g, y);
                if old_marker && new_marker {
                    continue;
                }
                let segment = format!("argument {} of {}", k + 1, quot_name(*f));
                if let Some(found) = step(g, x, y, names, path, segment) {
                    return Some(found);
                }
            }
            None
        }
        (Term::Meta(i), Term::Meta(j)) => (i != j).then(|| Found::here(old, new, names, path)),
        _ => Some(Found::here(old, new, names, path)),
    }
}

/// The head of `term`'s spine of applications, and how many arguments it's
/// applied to (as `hash.rs` counts them).
fn spine_head(term: &Term) -> (&Term, usize) {
    let mut term = term.strip_loc();
    let mut args = 0;
    while let Term::App(f, _, _) = term {
        args += 1;
        term = f.strip_loc();
    }
    (term, args)
}

/// A call's head and all its arguments, left to right, each with how it's
/// applied (the order the proofless hash writes them in).
fn full_spine(term: &Term) -> (&Term, Vec<(&Term, Icit)>) {
    let mut args = Vec::new();
    let mut head = term.strip_loc();
    while let Term::App(f, a, icit) = head {
        args.push((a.as_ref(), *icit));
        head = f.strip_loc();
    }
    args.reverse();
    (head, args)
}

/// Whether `term` as a whole is a proof the proofless hash leaves out.
fn is_proof(g: &Ev, term: &Term) -> bool {
    match spine_head(term).0 {
        Term::Def(id) => proof_positions(g, *id).is_some_and(|p| p.result),
        Term::Quot(QuotForm::Ind | QuotForm::Sound, _, _) => true,
        _ => false,
    }
}

/// Whether argument `k` (from 1) of a call of `head` is at a proof
/// position: the type of its parameter is a proposition.
fn proof_parameter(g: &Ev, head: &Term, k: usize) -> bool {
    let Term::Def(id) = head else {
        return false;
    };
    proof_positions(g, *id).is_some_and(|p| k > 0 && p.params.get(k - 1).copied().unwrap_or(false))
}

fn data_name(g: &Ev, d: DataId) -> String {
    g.env
        .datas()
        .get(d.0)
        .map(|data| data.path().to_string())
        .unwrap_or_else(|| format!("#{}", d.0))
}

fn ctor_name(g: &Ev, d: DataId, c: usize) -> String {
    g.env
        .datas()
        .get(d.0)
        .and_then(|data| data.ctors().get(c))
        .map(|ctor| ctor.name.to_string())
        .unwrap_or_else(|| format!("#{}", c))
}

fn call_name(g: &Ev, term: &Term) -> String {
    match spine_head(term).0 {
        Term::Def(id) => g
            .env
            .defs()
            .get(id.0)
            .map(|def| def.path().to_string())
            .unwrap_or_else(|| format!("#{}", id.0)),
        Term::Data(id, _) => data_name(g, *id),
        Term::Ctor(id, c, _) => ctor_name(g, *id, *c),
        Term::Var(_) => "a variable".to_string(),
        head => show(g, &[], head),
    }
}

fn quot_name(form: QuotForm) -> &'static str {
    match form {
        QuotForm::Type => "Quot",
        QuotForm::Mk => "Quot.mk",
        QuotForm::Lift => "Quot.lift",
        QuotForm::Ind => "Quot.ind",
        QuotForm::Sound => "Quot.sound",
    }
}

/// `term` printed with `names` (the old declaration's), cut short.
fn show(g: &Ev, names: &[Name], term: &Term) -> String {
    cut_to(&pretty::term_for_message(g, names, term), SHOWN)
}

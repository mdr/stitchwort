//! Termination checking for recursive definitions, and groups of definitions
//! that call each other, by size change (docs/proposals/mutual-recursion.md
//! §6).
//!
//! Every call from a member of the group to a member (itself or another) is
//! summarised as a size-change graph ([`crate::sct`]): for each of the
//! callee's parameters (its definition-entry arity, `Def::arity`), whether
//! the argument passed there is strictly smaller than (`<`), or at most
//! (`≤`), one of the caller's parameters, or unknown. The group is accepted
//! if every way of repeating its calls, in any order the calls allow, makes
//! some parameter strictly smaller ([`crate::sct::Group::check`]). So
//! lexicographic recursion (Ackermann's function), swapped arguments and a
//! wrapper that passes its argument on unchanged to a helper that makes it
//! smaller are accepted, as well as recursion that decreases the same
//! parameter in every call. Calls between *different* members are part of
//! the analysis exactly like calls to itself (Rocq's CVE-2026-72703 came from
//! leaving them out).
//!
//! An argument's relation comes only from the terms, never from types:
//!
//! - **`<`**: a variable bound as a field of a constructor matched (directly or
//!   through further matches) out of parameter `i`; a *recursive function
//!   field* (a field whose type is a function returning the matched data type,
//!   or another member of its data group, like `rest : res o -> Comp op res
//!   a`) applied to arguments, as in Rocq:
//!   each result is a child in the well-founded tree, and only the field
//!   variable itself counts, not some other function that happens to return
//!   the same type; and the constructor of such a descendant's match, applied
//!   to exactly the fields that match bound (in the branch where `m` is
//!   `Succ n`, `Succ n` *is* `m`), each field possibly rebuilt the same way
//!   (in the branch for `Cons x (Cons y (Cons z more))`, `Cons y (Cons z
//!   more)` is the tail); and a one-field constructor around a strict part
//!   ([`Walker::wrapped`]): `C u` where an enclosing match took `s` (`≤` or
//!   `<` parameter `i`) apart as `C v`, `C`'s type isn't a proposition, `C`
//!   has exactly one field, counting implicit, proof and erased ones, that
//!   field is relevant data (not a proof or a type), and `u` is reached from
//!   `v` by one or more matched fields of relevant data, never through a
//!   proof, a lambda's variable, a `let` or another function's result (after
//!   `MkText [c, ..r]`, `MkText r`; see "Relevant data only"). `s` itself
//!   may have been reached through a proof, by the first rule.
//! - **`≤`**: parameter `i` itself, or the constructor of a match on parameter
//!   `i` itself, rebuilt exactly as above. Both are equal to the parameter.
//! - **unknown**: anything else, including lambda-bound variables, other
//!   functions' results, `J` (transport never yields a part) and numbers.
//!   A `NumCase` binds nothing, so it adds no evidence.
//!
//! Each argument is related to at most one parameter, the one it was matched
//! out of, so each graph has at most one arc into each position.
//!
//! **The invariant** (docs/proposals/nested-data-types.md §6.4,
//! recursion-through-map.md §4): `<` relates two values only when, in every
//! run, the first's *rank* is below the second's, and `≤` only when it is
//! at most the second's. A value's rank is the height of its constructor
//! tree: one more than the least upper bound of its fields' ranks and of the
//! ranks of every result of its recursive function fields (an ordinal). A
//! field, a field of a field and so on, and a recursive function field
//! applied are below; a rebuilt constructor is equal; a one-field `C u` is
//! rank(`u`) + 1, below rank(`v`) + 1 = rank(`s`) when `u` is strictly
//! inside `v`. The last two hold only up to proof positions: see "Two
//! orders". Evidence comes from the terms of one particular value, never
//! from a relation computed from the data types. So for
//! a nested type (`Packets (items: List Packet)`), that `Packet`, `List
//! Packet` and `Packet` again repeat in the *types* doesn't matter: for
//! values, `p > items > q`, and `q` is never `p`. The one type-directed step
//! is recognising a recursive function field, which reads the matched type's
//! own declared field and its own group, so a field like `kids: Nat → List
//! Tree` (which returns a `List`, not a member) gains nothing. Quotients
//! can't be matched (a quotient form gives no evidence of descent).
//!
//! Why that's sound, assuming that every data type's values are well
//! founded, that is, contain no infinite chain of constructor subvalues, so
//! that every value has a rank: a decrease in every way of repeating the
//! calls would then be an infinite descent of ordinals. For a type that is
//! strictly positive and not nested this is standard. For a nested type it
//! rests on the type being isomorphic to its mutual encoding (the type with
//! a private copy of each container), whose values are well founded; that
//! isomorphism is the usual constructor-for-constructor relabelling,
//! believed but not proved for Stitchwort (nested-data-types.md §6.3, C1).
//!
//! **Two orders** (docs/reviews/SW-3412-text-rest-relanded.md §3, F1;
//! docs/reviews/SW-3376-wrapper-rule-soundness.md F2). Rank as above is read
//! on the terms the kernel evaluates, proofs included: *term rank*.
//! *Relevant rank* is the same height with every proof position counted as
//! nothing: what conversion can see, and what a run sees after erasure. The
//! plain field rule keeps term rank. A rebuilt constructor, and with it the
//! one-field rule, keep only relevant rank: a field pinned by a later
//! field's type may be any term ([`Walker::rebuilt`]), and where the pinning
//! type takes it at a proof position, which comparison skips, the rebuilt
//! value can hold anything there. In
//! `examples/accept/termination-pinned-proof-replaced.sw`, `f (MkW (Mk
//! (MkAny (MkW (In (In (Mk p x))))) x))` from `f (MkW (In (Mk p x)))` is
//! recorded `<`: its relevant rank is lower, but its term rank is higher,
//! since the proof holds a value bigger than the argument. The two orders
//! can be mixed only because a value put into a pinned proof never comes
//! back onto the thread: taking it out would need the proof's type to be
//! able to hold the type being matched, and a pinned field's type can't
//! mention that type or its group, directly (`E-POSITIVITY`: no field
//! depends on an earlier one that holds a member) or through nesting
//! (nestable parameters, conditions 2 and 5); a proposition that hides the
//! type (`MkAny [a: Type] (x: a)`) gives back a value of an unknown type,
//! and types are never taken apart. So **termination depends on those
//! positivity rules**: without them a looping definition passes, every call
//! recorded smaller (`examples/soundness/termination-relies-on-positivity-*.sw`;
//! with the direct rule and condition 2 both removed by hand, 01 and 04 are
//! accepted and `byComputing` on 04 never finishes; `reject/termination-rebuilt-pinned-proof.sw`
//! is a refused loop whose error names such a false `<`). Which order
//! counts: a function that returns data takes apart only proofs whose
//! fields are all proofs (`E-PROP-ELIM`, D1980), so every data argument it
//! passes was reached through data, and relevant rank decides; a function
//! that returns a proof never runs, and the kernel's evaluation of it ends
//! by term rank on closed proofs (it never swaps one proof for another) and
//! at a stuck `case` on open ones.
//!
//! **On open terms** (the unfolding policy, docs/core.md), an accepted cycle
//! can't unfold for ever, but not because some `case` on the way is always
//! stuck: with eta records on the whole chain, and the type changing from
//! call to call, none is (`examples/accept/termination-wrapper-changing-instance.sw`,
//! where only a `case` on a type equation outside the chain stops it). The
//! reason (docs/reviews/SW-3376-wrapper-rule-soundness.md §3.1) is a size
//! of open values: a constructor is one more than the sum of its fields'
//! sizes, and an unknown of type `A` counts as `A`'s eta depth (1 plus the
//! sum over its fields' types if `A` is an eta record, else 0). A `case`
//! that fires lowers it: it takes away a constructor, or one eta layer of an
//! unknown. Every `<` comes from cases that fired (a `≤` keeps the value),
//! and `C u` has size 1 + size(`u`), below 1 + size(`v`), whether `s` was a
//! constructor or an unknown of an eta type. So each turn of an accepted
//! cycle lowers the size of the value on its thread, or is stuck. Eta depth is finite because eta
//! records aren't recursive, index unification solves with an occurs check
//! and never takes a type former apart, and a type computed from a proof
//! needs a proposition that doesn't mention itself (D1980). That is also
//! why the steps from `v` to `u` must be matched fields: a lambda's variable
//! or an accessor's result has no `case` behind it (the review of SW-3359,
//! R7.3).
//!
//! **Relevant data only** (the one-field rule's conditions on proofs). Rank
//! reads the terms the kernel evaluates, proofs included, but conversion
//! skips proofs (docs/proposals/proof-irrelevance.md §7.1) and a run erases
//! them, so a `case` on one takes its branch without looking. Where `C`'s
//! one field is a proof (`MkBox (h: Loop)`), or `C`'s type is a
//! proposition (`MkSquash (x: List Nat)`), every `C x` of one type is the
//! same value to the kernel, and calling `f (MkBox n)` from `f b` with `n` a
//! part of `b`'s proof is calling `f` on its own argument: the descent is
//! one the evaluator's equality can't see, the trap of Agda #8699
//! (`examples/soundness/proof-irrelevance-07-descent-through-a-proof.sw`;
//! the lesson in docs/proposals/mutual-recursion.md §6.7, that the order
//! must agree with conversion). The same goes for a part reached through a
//! proof anywhere on the way from `v` to `u`: it's a part of a proof. So
//! the one field and every step from `v` to `u` must be a field of relevant
//! data ([`Binder::relevant`]): the wrapper's own shrinking must be visible
//! in data. Where `s` sits needn't be: it may be inside a proof, reached
//! from the parameter by the plain field rule
//! (`examples/accept/termination-wrapper-inside-proof.sw`). That's harmless,
//! since a match on a proof's data field can only produce a proof
//! (`E-PROP-ELIM`), so the function returns a proof and never runs, and the
//! kernel evaluates it only on a proof it holds, where `s` really is a
//! part. The other condition stays as it was, every
//! field counting towards "one field", proofs included: the rank argument
//! needs rank(`C u`) = rank(`u`) + 1 in both orders, and a field of a proof is
//! a part of its value for the plain rule, so a proof beside `u` can carry a
//! bigger value back (`examples/reject/termination-wrapper-proof-beside.sw`
//! loops if `MkD xs q` counts as one field). Recursion on a proof itself
//! (`Loop → Void` by `MkLoop n => f n`) is a plain field, not this rule,
//! and stays allowed (D1980).
//!
//! **Every occurrence of a member is a call**, wherever it is: under lambdas,
//! inside types and inside the arguments of other calls. Each application
//! spine headed by a member is one call, with its own graph, never merged
//! with another (even one with the same caller and callee); all its
//! arguments are then walked for further calls, including any beyond the
//! arity. **Occurrences of members must be saturated**: applied to at least
//! the callee's entry arity's arguments, so that the call's graph says what
//! every parameter is given. A bare or partial occurrence is refused, with a
//! suggestion to write `x => f a x` (§6.3).
//!
//! **A lifted `match` occurring exactly once, in another member, is
//! inlined** there: its body is walked at that occurrence, with each
//! parameter standing for its argument, rather than being a call of its own.
//! So it sees the patterns around the place it's written: in it, `Cons y
//! more` rebuilt from the fields of an enclosing pattern is still that part.

use crate::ev::Ev;
use stitchwort_syntax::{Diagnostic, Span};

use crate::budget::ResourceError;
use crate::pretty;
use crate::sct::{self, Label, Outcome};
use crate::term::{DataId, DefId, Icit, Name, Sort, Term};

/// Checks that `body`, the checked body of definition `self_id` (which hasn't
/// got a body yet), terminates: a group of one.
pub fn check(
    g: &Ev,
    body: &Term,
    self_id: DefId,
    name: &str,
    span: Span,
) -> Result<(), Diagnostic> {
    check_with_limit(g, body, self_id, name, span, sct::MAX_GRAPHS)
}

/// [`check`], allowing at most `max_graphs` distinct graphs in the closure of
/// the calls.
pub fn check_with_limit(
    g: &Ev,
    body: &Term,
    self_id: DefId,
    name: &str,
    span: Span,
    max_graphs: usize,
) -> Result<(), Diagnostic> {
    check_members(g, &[(self_id, body, name, span)], max_graphs)
}

/// A member of a group being checked: a definition (pending, with its arity
/// set) and its checked body.
pub struct Member<'a> {
    pub id: DefId,
    pub body: &'a Term,
}

/// Checks that the members of a group terminate together: every call from
/// any member to any member is in the analysis. Allows at most `max_graphs`
/// distinct graphs in the closure of the calls.
pub fn check_group(g: &Ev, members: &[Member], max_graphs: usize) -> Result<(), Diagnostic> {
    let members: Vec<(DefId, &Term, &str, Span)> = members
        .iter()
        .map(|m| {
            let def = g.def(m.id);
            (m.id, m.body, &*def.name, def.span)
        })
        .collect();
    check_members(g, &members, max_graphs)
}

/// The parameters of a member: its entry lambdas' names and implicitness.
type Params = Vec<(Name, Icit)>;

/// What the error messages need to know about a member.
struct MemberInfo<'a> {
    name: &'a str,
    params: Params,
    span: Span,
    /// Its result type, after the parameters, is `Std.Stream` of
    /// something.
    returns_stream: bool,
}

/// Whether a definition's type, after its parameters, is `Stream a`.
fn returns_stream(g: &Ev, id: DefId) -> bool {
    let mut ty = g.def(id).ty.strip_loc();
    while let Term::Pi(_, _, _, body, _) = ty {
        ty = body.strip_loc();
    }
    matches!(ty, Term::Data(d, _) if &*g.data(*d).path == "Std.Stream")
}

fn check_members(
    g: &Ev,
    members: &[(DefId, &Term, &str, Span)],
    max_graphs: usize,
) -> Result<(), Diagnostic> {
    let ids: Vec<DefId> = members.iter().map(|m| m.0).collect();
    let mut infos = Vec::new();
    let mut trees = Vec::new();
    for &(id, body, name, span) in members {
        let arity = g.def(id).arity;
        if body.count_lams() != arity {
            return Err(Diagnostic::error(
                "E-MALFORMED",
                format!(
                    "malformed core term: `{name}`'s body doesn't start with its {arity} \
                     parameters"
                ),
            )
            .with_label(span, "in this definition")
            .with_note("this is a bug in the compiler, not in your program"));
        }
        let mut params = Vec::new();
        let mut tree = body;
        // The innermost location around what's left after the parameters:
        // for a body that's just a call, that call's own span, so a failing
        // call in it is labelled precisely.
        let mut tree_span = span;
        loop {
            match tree {
                Term::Loc(loc, inner) => {
                    tree_span = *loc;
                    tree = inner.as_ref();
                }
                Term::Lam(x, icit, inner, _) => {
                    params.push((x.clone(), *icit));
                    tree = inner.as_ref();
                }
                _ => break,
            }
        }
        infos.push(MemberInfo {
            name,
            params,
            span,
            returns_stream: returns_stream(g, id),
        });
        trees.push((tree, tree_span));
    }
    let inlined = inlined(&ids, &infos, &trees);
    let mut calls = Vec::new();
    let mut matched_params = Vec::new();
    for (from, &(tree, tree_span)) in trees.iter().enumerate() {
        let params = &infos[from].params;
        let mut walker = Walker {
            g,
            members: &ids,
            infos: &infos,
            trees: &trees,
            inlined: &inlined,
            from,
            vars: params
                .iter()
                .enumerate()
                .map(|(i, (x, _))| Info {
                    name: x.clone(),
                    param: Some(i),
                    smaller_than: None,
                    recursive_fn: false,
                    alias: None,
                    parent: None,
                })
                .collect(),
            calls: Vec::new(),
            matched: Vec::new(),
            matched_params: vec![false; params.len()],
            span: tree_span,
        };
        if !inlined[from] {
            walker.walk(tree)?;
        }
        calls.extend(walker.calls);
        matched_params.push(walker.matched_params);
    }

    let mut group = sct::Group::new(infos.iter().map(|m| m.params.len()).collect());
    for call in &calls {
        group
            .call(call.from, call.to, &call.arcs)
            .expect("internal error: a call's arcs are within the arities");
    }
    match group.check(&g.machine.budget, max_graphs) {
        Ok(Outcome::Terminates) => Ok(()),
        Ok(Outcome::NoDescent { path, graph }) => Err(no_descent(
            g,
            &infos,
            &matched_params,
            &inlined,
            &calls,
            &path,
            graph.entries(),
        )),
        Err(e) => Err(inconclusive(e, &infos)),
    }
}

/// Which members are inlined: lifted `match`es (`f.%match1`) occurring
/// exactly once in the group's bodies, in another member, except that where
/// following those occurrences leads round a cycle, the first member on it
/// isn't. Inlining any member would be as sound; definitions written as such
/// are left as calls so that messages go round them as written.
fn inlined(ids: &[DefId], infos: &[MemberInfo], trees: &[(&Term, Span)]) -> Vec<bool> {
    let mut occurrences: Vec<Vec<usize>> = vec![Vec::new(); ids.len()];
    for (from, (tree, _)) in trees.iter().enumerate() {
        for (term, _) in tree.subterms() {
            if let Term::Def(id) = term
                && let Some(to) = ids.iter().position(|m| m == id)
            {
                occurrences[to].push(from);
            }
        }
    }
    let mut inlined: Vec<bool> = occurrences
        .iter()
        .enumerate()
        .map(|(m, from)| {
            let lifted = infos[m]
                .name
                .rsplit('.')
                .next()
                .is_some_and(|last| last.starts_with("%match"));
            lifted && matches!(from[..], [from] if from != m)
        })
        .collect();
    for m in 0..ids.len() {
        let mut at = m;
        for _ in 0..ids.len() {
            if !inlined[at] {
                break;
            }
            at = occurrences[at][0];
            if at == m {
                inlined[m] = false;
                break;
            }
        }
    }
    inlined
}

/// A call from one member to another (or itself): an arc `(caller position,
/// callee position, label)` for each argument related to a parameter, and
/// where it is.
struct Call {
    from: usize,
    to: usize,
    arcs: Vec<(usize, usize, Label)>,
    span: Span,
    /// The arguments given for the callee's parameters, and the names in
    /// scope, for the error.
    args: Vec<Term>,
    names: Vec<Name>,
}

struct Info {
    name: Name,
    /// This variable is parameter `i` of the definition.
    param: Option<usize>,
    /// This variable is structurally smaller than parameter `i`.
    smaller_than: Option<usize>,
    /// This variable is a recursive function field of a matched constructor.
    recursive_fn: bool,
    /// For a parameter of an inlined member, the variable its argument is
    /// equal to ([`Walker::rebuilt`]).
    alias: Option<(usize, Pins)>,
    /// For a relevant field bound by a `case` ([`Binder::relevant`]), the
    /// level of the variable it was matched out of: in every run its value
    /// is a field of that variable's value. Only `case` sets it, never a
    /// `let`, a lambda or an inlined parameter, so following it goes through
    /// matched fields only ([`Walker::strictly_inside`]), and never through
    /// a proof: comparison skips proofs, so a part of one isn't smaller
    /// than anything conversion can tell apart (the header, "Relevant data
    /// only").
    parent: Option<usize>,
}

/// A variable [`Walker::under`] binds.
struct Binder {
    name: Name,
    /// It's a recursive function field of a matched constructor.
    recursive_fn: bool,
    /// It's relevant data: a field that isn't a proof or a type, of a
    /// constructor of a type that isn't a proposition. Only such a field is
    /// a part for rule 3 ([`Info::parent`]).
    relevant: bool,
}

impl Binder {
    /// A lambda's or a Π's variable.
    fn plain(name: &Name) -> Binder {
        Binder {
            name: name.clone(),
            recursive_fn: false,
            relevant: false,
        }
    }
}

/// Walks the body of member `from`, recording its calls.
struct Walker<'a> {
    g: &'a Ev<'a>,
    /// The group's members, by position.
    members: &'a [DefId],
    infos: &'a [MemberInfo<'a>],
    /// Each member's body after its parameters, and its span.
    trees: &'a [(&'a Term, Span)],
    /// Which members are walked where they occur ([`inlined`]).
    inlined: &'a [bool],
    from: usize,
    /// The variables in scope, indexed by de Bruijn level.
    vars: Vec<Info>,
    calls: Vec<Call>,
    /// The case branches we're inside: the variable matched (a level), and
    /// the constructor and the levels of its fields in this branch.
    matched: Vec<Matched>,
    /// Which of the member's parameters are matched on, directly or through
    /// their parts.
    matched_params: Vec<bool>,
    span: Span,
}

struct Matched {
    scrutinee: usize,
    data: DataId,
    ctor: usize,
    fields: std::ops::Range<usize>,
}

/// Whether a field of a constructor of data type `d` is a function returning
/// `d` or another member of its data group (the group's metadata, fixed when
/// it was declared). Strict positivity across the group makes each result a
/// part of the matched value.
fn is_recursive_fn(g: &Ev, ty: &Term, d: DataId) -> bool {
    let mut ty = ty.strip_loc();
    let mut arrows = 0;
    while let Term::Pi(_, _, _, cod, _) = ty {
        arrows += 1;
        ty = cod.strip_loc();
    }
    arrows > 0 && matches!(ty, Term::Data(d2, _) if g.data(d).group.contains(d2))
}

/// Which arguments of a rebuilt term's type are known to be those of the
/// matched value's type.
#[derive(Clone, Copy)]
enum Pins {
    All,
    Indices,
    Nothing,
}

/// Whether field type `ty` is a data type with variable `ix` as one of the
/// arguments `pins` says are known.
fn pins_var(g: &Ev, ty: &Term, ix: usize, pins: Pins) -> bool {
    let Term::Data(d, args) = ty.strip_loc() else {
        return false;
    };
    let first = match pins {
        Pins::All => 0,
        Pins::Indices => g.data(*d).params.len(),
        Pins::Nothing => return false,
    };
    args.iter()
        .skip(first)
        .any(|a| matches!(a.strip_loc(), Term::Var(i) if *i == ix))
}

impl Walker<'_> {
    fn walk(&mut self, term: &Term) -> Result<(), Diagnostic> {
        self.g.machine.budget.nesting("termination checker")?;
        match term {
            Term::Loc(span, inner) => {
                let saved = self.span;
                self.span = *span;
                let result = self.walk(inner);
                self.span = saved;
                result?;
            }
            // A compact list is closed, and makes no calls. It's never related
            // to a parameter (`relate`): descent comes only from matching,
            // where a range's tail is a field of the `Cons` its expansion
            // has, exactly as for an ordinary list.
            Term::Var(_)
            | Term::Nat(_)
            | Term::Chars(_)
            | Term::Sort(_)
            | Term::Refl
            | Term::Meta(_) => {}
            Term::Def(id) => {
                if let Some(to) = self.member(*id) {
                    self.occurrence(to, &[])?;
                }
            }
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head
                    && let Some(to) = self.member(*id)
                {
                    // One call for the whole spine; the head isn't walked
                    // again, or it would count as a bare reference too.
                    self.occurrence(to, &args)?;
                } else {
                    self.walk(head)?;
                }
                for arg in args {
                    self.walk(arg)?;
                }
            }
            Term::Lam(x, _, body, _) => self.under(&[Binder::plain(x)], None, None, body)?,
            Term::Pi(x, _, dom, cod, _) => {
                self.walk(dom)?;
                self.under(&[Binder::plain(x)], None, None, cod)?;
            }
            // A quotient form, `Quot.lift` included, gives no evidence of
            // descent (it isn't a match), like `J`: calls in its arguments
            // are checked as any call (docs/proposals/map-equality.md §7.5).
            Term::Data(_, args) | Term::Ctor(_, _, args) | Term::Quot(_, args, _, _) => {
                for arg in args {
                    self.walk(arg)?;
                }
            }
            Term::Ann(e, t) => {
                self.walk(e)?;
                self.walk(t)?;
            }
            // `let x := v` is exactly as small as `v`: `x` gets the relation
            // `v` has, from the terms alone, and nothing more
            // (docs/proposals/let.md §6.1 rule 3). Calls are looked for in
            // the annotation, the value and the body.
            Term::Let(x, ty, value, body, _, _) => {
                self.walk(ty)?;
                self.walk(value)?;
                let (param, smaller_than) = match self.relate(value) {
                    Some((i, Label::Le)) => (Some(i), None),
                    Some((i, Label::Lt)) => (None, Some(i)),
                    None => (None, None),
                };
                self.vars.push(Info {
                    name: x.clone(),
                    param,
                    smaller_than,
                    recursive_fn: false,
                    alias: None,
                    parent: None,
                });
                let result = self.walk(body);
                self.vars.pop();
                result?;
            }
            Term::Case(ix, d, branches) => {
                let scrutinee = &self.vars[self.vars.len() - 1 - ix];
                let source = scrutinee.param.or(scrutinee.smaller_than);
                if let Some(i) = source {
                    self.matched_params[i] = true;
                }
                let level = self.vars.len();
                let g = self.g;
                for (c, branch) in branches.iter().enumerate() {
                    self.matched.push(Matched {
                        scrutinee: level - 1 - ix,
                        data: *d,
                        ctor: c,
                        fields: level..level + branch.names.len(),
                    });
                    // Only relevant data is a part for rule 3's chains: a
                    // proposition's fields, and a proof or type field of
                    // anything, get no parent ([`Info::parent`]).
                    let data = g.data(*d);
                    let ctor = &data.ctors[c];
                    let fields: Vec<Binder> = branch
                        .names
                        .iter()
                        .zip(&ctor.fields)
                        .zip(&ctor.field_erased)
                        .map(|((x, (_, ty)), erased)| Binder {
                            name: x.clone(),
                            recursive_fn: is_recursive_fn(g, ty, *d),
                            relevant: data.sort != Sort::Prop && !erased,
                        })
                        .collect();
                    // An impossible branch has nothing to walk.
                    let result = match &branch.body {
                        Some(body) => self.under(&fields, source, Some(level - 1 - ix), body),
                        None => Ok(()),
                    };
                    self.matched.pop();
                    result?;
                }
            }
            // A number case binds nothing and makes nothing smaller, but every
            // arm and the default are walked, keeping what's already known.
            Term::NumCase(_, arms, default) => {
                for arm in arms.iter() {
                    self.walk(&arm.body)?;
                }
                self.walk(default)?;
            }
            Term::Eq(ty, a, b) => {
                if let Some(ty) = ty {
                    self.walk(ty)?;
                }
                self.walk(a)?;
                self.walk(b)?;
            }
            Term::J(m, b, p, _) => {
                self.walk(m)?;
                self.walk(b)?;
                // A cast's ends, which the kernel adds from its proof's
                // type, are only compared, never run: calls in them are no
                // more calls than ones in that type, which isn't walked.
                match (Term::j_ends(p), p.strip_loc()) {
                    (Some(_), Term::Ann(proof, _)) => self.walk(proof)?,
                    _ => self.walk(p)?,
                }
            }
            // A projection gives no evidence of descent here (`relate`
            // doesn't look through it): conservative, never unsound.
            Term::Proj(_, _, t) => self.walk(t)?,
        }
        Ok(())
    }

    /// The position in the group of definition `id`, if it's a member.
    fn member(&self, id: DefId) -> Option<usize> {
        self.members.iter().position(|m| *m == id)
    }

    /// Records an occurrence of member `to` applied to `args`: a call, if
    /// it's given all of `to`'s parameters, or its body walked here if it's
    /// inlined. Arguments beyond them get no entry in the graph (the caller
    /// still walks them).
    fn occurrence(&mut self, to: usize, args: &[&Term]) -> Result<(), Diagnostic> {
        let arity = self.infos[to].params.len();
        if args.len() < arity {
            return Err(self.unsaturated(to, args));
        }
        let args = &args[..arity];
        if self.inlined[to] {
            return self.inline(to, args);
        }
        let arcs = args
            .iter()
            .enumerate()
            .filter_map(|(j, arg)| self.relate(arg).map(|(i, label)| (i, j, label)))
            .collect();
        self.calls.push(Call {
            from: self.from,
            to,
            arcs,
            span: self.span,
            args: args.iter().map(|a| (*a).clone()).collect(),
            names: self.vars.iter().map(|info| info.name.clone()).collect(),
        });
        Ok(())
    }

    /// Walks the body of member `to` where it's applied to `args`: each
    /// parameter is as small as its argument, and equal to the variable the
    /// argument is, if any.
    fn inline(&mut self, to: usize, args: &[&Term]) -> Result<(), Diagnostic> {
        let params: Vec<Info> = args
            .iter()
            .zip(&self.infos[to].params)
            .map(|(arg, (x, _))| {
                let (param, smaller_than) = match self.relate(arg) {
                    Some((i, Label::Le)) => (Some(i), None),
                    Some((i, Label::Lt)) => (None, Some(i)),
                    None => (None, None),
                };
                let recursive_fn = match arg.strip_loc() {
                    Term::Var(ix) => self
                        .vars
                        .len()
                        .checked_sub(1 + ix)
                        .is_some_and(|level| self.vars[level].recursive_fn),
                    _ => false,
                };
                Info {
                    name: x.clone(),
                    param,
                    smaller_than,
                    recursive_fn,
                    alias: self.rebuilt(arg),
                    parent: None,
                }
            })
            .collect();
        let depth = self.vars.len();
        self.vars.extend(params);
        let (tree, span) = self.trees[to];
        let saved = std::mem::replace(&mut self.span, span);
        let result = self.walk(tree);
        self.span = saved;
        self.vars.truncate(depth);
        result
    }

    /// The parameter `arg` is related to, and how, if it's one of: a
    /// parameter, a variable matched from one, a recursive function field
    /// applied to arguments, or a constructor rebuilding a matched value.
    fn relate(&self, arg: &Term) -> Option<(usize, Label)> {
        let level = self.vars.len();
        let info = |ix: usize| self.vars.get(level.checked_sub(ix + 1)?);
        let related = |info: &Info| match (info.param, info.smaller_than) {
            (Some(i), _) => Some((i, Label::Le)),
            (None, Some(i)) => Some((i, Label::Lt)),
            (None, None) => None,
        };
        match arg.strip_loc() {
            Term::Var(ix) => related(info(*ix)?),
            Term::App(..) => {
                let Term::Var(ix) = arg.spine().0 else {
                    return None;
                };
                let info = info(*ix)?;
                if info.recursive_fn {
                    info.smaller_than.map(|i| (i, Label::Lt))
                } else {
                    None
                }
            }
            Term::Ctor(..) => self
                .rebuilt(arg)
                .and_then(|(level, _)| related(&self.vars[level]))
                .or_else(|| self.wrapped(arg)),
            _ => None,
        }
    }

    /// A one-field constructor around a strict part (rule 3,
    /// docs/proposals/recursion-through-map.md §3, D3612): `C u` is smaller
    /// than whatever `s` is at most, if an enclosing match took `s` apart as
    /// `C v`, `C`'s type isn't a proposition, `C` has exactly one field
    /// (implicit, proof and erased fields count, so `MkChar code valid` has
    /// two) which is relevant data and isn't a recursive function field, and
    /// `u` is strictly inside `v` through relevant fields
    /// ([`Walker::part_of`], [`Walker::strictly_inside`]; the header,
    /// "Relevant data only"). Read as rank,
    /// the height of a value's constructor tree: rank(`C u`) = rank(`u`) + 1
    /// < rank(`v`) + 1 = rank(`s`). So `MkText r` with `r` a tail of the
    /// matched text's characters is smaller than the text.
    fn wrapped(&self, term: &Term) -> Option<(usize, Label)> {
        let Term::Ctor(d, c, args) = term.strip_loc() else {
            return None;
        };
        let [u] = &args[..] else {
            return None;
        };
        // A recursive function field as the one field would break rank(`C
        // v`) = rank(`v`) + 1: `Sup kids`'s rank is above every result of
        // `kids`, not above `kids`.
        // A proof or type as the one field, or a proposition as `C`'s type,
        // would make every `C x` of one type the same value to conversion,
        // which skips proofs: no `C u` is smaller than `C v` there (the
        // header, "Relevant data only").
        let data = self.g.data(*d);
        let ctor = &data.ctors[*c];
        if ctor.fields.len() != 1
            || ctor.field_erased[0]
            || data.sort == Sort::Prop
            || is_recursive_fn(self.g, &ctor.fields[0].1, *d)
        {
            return None;
        }
        let inner = self.part_of(u)?;
        self.matched.iter().rev().find_map(|m| {
            if m.data != *d || m.ctor != *c || !self.strictly_inside(inner, m.fields.start) {
                return None;
            }
            let s = &self.vars[m.scrutinee];
            s.param.or(s.smaller_than).map(|i| (i, Label::Lt))
        })
    }

    /// The level of a variable whose strict parts include `u`'s value, or
    /// are it: `u` itself if it's a variable or a rebuilt constructor (then
    /// equal to that variable), or for a recursive function field applied
    /// (`rest y`), the field (`rest y` is then strictly inside the value
    /// `rest` was matched out of, so to be strictly inside `v`, `rest` must
    /// be too). Nothing else: not a lambda's variable applied, nor any other
    /// function's result (an accessor's included).
    fn part_of(&self, u: &Term) -> Option<usize> {
        match u.strip_loc() {
            Term::App(..) => {
                let Term::Var(ix) = u.spine().0 else {
                    return None;
                };
                let level = self.vars.len().checked_sub(ix + 1)?;
                let info = &self.vars[level];
                info.recursive_fn
                    .then(|| info.alias.map_or(level, |(l, _)| l))
            }
            _ => self.rebuilt(u).map(|(level, _)| level),
        }
    }

    /// Whether the variable at `level` is strictly inside the one at `v`:
    /// reached from it by one or more matched fields of relevant data,
    /// following [`Info::parent`] (through inlined parameters to the
    /// variables they equal).
    fn strictly_inside(&self, level: usize, v: usize) -> bool {
        let resolve = |l: usize| self.vars[l].alias.map_or(l, |(a, _)| a);
        let v = resolve(v);
        let mut at = resolve(level);
        while let Some(parent) = self.vars[at].parent {
            at = resolve(parent);
            if at == v {
                return true;
            }
        }
        false
    }

    /// The level of the variable `term` is equal to: a variable itself, or a
    /// constructor applied to exactly the fields an enclosing match bound for
    /// it, each of which may itself be rebuilt. So in the branch for
    /// `Cons x (Cons y (Cons z more))`, `Cons y (Cons z more)` is the first
    /// match's tail. An inlined member's parameter is its argument's variable.
    ///
    /// A field pinned by a later field's type (`n` in `VCons (x: a) (xs: Vec
    /// a n)`) may be any term, if the later field is rebuilt: the body has
    /// type-checked, so the later field's type, and with it the pinned field,
    /// equals the matched one's. The elaborator often fills such a field with
    /// what the match's index unification solved it to, `Succ m` rather than
    /// `n`. A variable's type is known exactly, so it pins through any
    /// argument of its type; a rebuilt constructor's indices are known only
    /// if its result's indices don't depend on the parameters (which come
    /// from wherever it's used), and its parameters not at all.
    fn rebuilt(&self, term: &Term) -> Option<(usize, Pins)> {
        let resolve = |level: usize| self.vars[level].alias.map_or(level, |(l, _)| l);
        match term.strip_loc() {
            Term::Var(ix) => {
                let level = self.vars.len().checked_sub(ix + 1)?;
                Some(self.vars[level].alias.unwrap_or((level, Pins::All)))
            }
            Term::Ctor(d, c, args) => {
                let data = self.g.data(*d);
                let ctor = &data.ctors[*c];
                let fields: Vec<Option<(usize, Pins)>> =
                    args.iter().map(|a| self.rebuilt(a)).collect();
                let m = self.matched.iter().rev().find(|m| {
                    let field = |j: usize| match fields[j] {
                        Some((level, pins)) if level == resolve(m.fields.start + j) => Some(pins),
                        _ => None,
                    };
                    m.data == *d
                        && m.ctor == *c
                        && m.fields.len() == fields.len()
                        && (0..fields.len()).all(|j| {
                            field(j).is_some()
                                || (j + 1..fields.len()).any(|k| {
                                    field(k).is_some_and(|pins| {
                                        pins_var(self.g, &ctor.fields[k].1, k - 1 - j, pins)
                                    })
                                })
                        })
                })?;
                let n = ctor.fields.len();
                let free_of_params = ctor
                    .result
                    .iter()
                    .all(|r| (0..data.params.len()).all(|p| !r.mentions(n + p)));
                let pins = if free_of_params {
                    Pins::Indices
                } else {
                    Pins::Nothing
                };
                Some((resolve(m.scrutinee), pins))
            }
            _ => None,
        }
    }

    /// Walks `body` under new binders. `parent` is the level of the variable
    /// a match took apart to bind them, if they're its fields; it's recorded
    /// only for the relevant ones.
    fn under(
        &mut self,
        binders: &[Binder],
        smaller_than: Option<usize>,
        parent: Option<usize>,
        body: &Term,
    ) -> Result<(), Diagnostic> {
        for binder in binders {
            self.vars.push(Info {
                name: binder.name.clone(),
                param: None,
                smaller_than,
                recursive_fn: binder.recursive_fn,
                alias: None,
                parent: parent.filter(|_| binder.relevant),
            });
        }
        let result = self.walk(body);
        self.vars.truncate(self.vars.len() - binders.len());
        result
    }

    /// The error for an occurrence of member `to` given only `args`,
    /// suggesting a lambda that takes the rest.
    fn unsaturated(&self, to: usize, args: &[&Term]) -> Diagnostic {
        let MemberInfo { name, params, .. } = &self.infos[to];
        let explicit =
            |params: &[(Name, Icit)]| params.iter().filter(|(_, i)| *i == Icit::Explicit).count();
        let (given, missing) = params.split_at(args.len());
        let names: Vec<Name> = self.vars.iter().map(|info| info.name.clone()).collect();
        let mut fresh = Vec::new();
        for _ in 0..explicit(missing) {
            let taken =
                |x: &str| names.iter().any(|n| &**n == x) || fresh.iter().any(|n: &String| n == x);
            let x = ["x", "y", "z"]
                .into_iter()
                .map(String::from)
                .chain((1..).map(|k| format!("x{k}")))
                .find(|x| !taken(x))
                .expect("there's always a fresh name");
            fresh.push(x);
        }
        let mut call = name.to_string();
        for (arg, (_, icit)) in args.iter().zip(given) {
            if *icit == Icit::Explicit {
                // An argument with a space in it needs parentheses here.
                let arg = pretty::term(self.g, &names, arg);
                if arg.contains(' ') {
                    call.push_str(&format!(" ({arg})"));
                } else {
                    call.push_str(&format!(" {arg}"));
                }
            }
        }
        let suggestion = format!("{} => {call} {}", fresh.join(" "), fresh.join(" "));
        let (wanted, got) = (explicit(params), explicit(given));
        let plural = |n: usize| if n == 1 { "argument" } else { "arguments" };
        let label = if args.is_empty() {
            format!(
                "`{name}` takes {wanted} {}; it's given none here",
                plural(wanted)
            )
        } else {
            format!(
                "`{name}` takes {wanted} {}; it's given {got}",
                plural(wanted)
            )
        };
        Diagnostic::error(
            "E-TERMINATION",
            format!("`{name}` is used here without all its arguments"),
        )
        .with_label(self.span, label)
        .with_note(format!("write `{suggestion}` so the call can be checked"))
        .with_note(if self.members.len() > 1 {
            "a call between definitions that call each other must be given all the arguments, so \
             the termination checker can see what each one is"
        } else {
            "a recursive call must be given all the arguments, so the termination checker can \
             see what each one is"
        })
    }
}

/// The error for a cycle of calls (`path`, composing to `entries`) in which
/// no parameter gets smaller.
fn no_descent(
    g: &Ev,
    members: &[MemberInfo],
    matched_params: &[Vec<bool>],
    inlined: &[bool],
    calls: &[Call],
    path: &[sct::CallId],
    entries: &[Option<sct::Arc>],
) -> Diagnostic {
    // The members on the cycle, in the order it visits them.
    let mut on_cycle: Vec<usize> = Vec::new();
    for &c in path {
        if !on_cycle.contains(&calls[c].from) {
            on_cycle.push(calls[c].from);
        }
    }
    let quoted = |m: usize| format!("`{}`", members[m].name);
    let message = match &on_cycle[..] {
        [m] => format!("can't show that {} terminates", quoted(*m)),
        ms => {
            let (last, rest) = ms.split_last().expect("a cycle has a member");
            let rest: Vec<String> = rest.iter().map(|m| quoted(*m)).collect();
            format!(
                "can't show that {} and {} terminate",
                rest.join(", "),
                quoted(*last)
            )
        }
    };
    let mut diagnostic = Diagnostic::error("E-TERMINATION", message);
    // Inlined members make no calls of their own.
    let single = inlined.iter().filter(|inlined| !**inlined).count() == 1;
    let mut labelled: Vec<sct::CallId> = Vec::new();
    for &c in path {
        if labelled.contains(&c) {
            continue;
        }
        let call = &calls[c];
        let (from, to) = (&members[call.from], &members[call.to]);
        let what = if to.params.is_empty() {
            if single {
                format!(
                    "`{}` has no parameters, so nothing can get smaller",
                    to.name
                )
            } else {
                format!(
                    "`{}` takes no arguments, so nothing can get smaller",
                    to.name
                )
            }
        } else {
            not_smaller(g, from, to, &matched_params[call.to], call)
                .unwrap_or_else(|| describe(from, to, call.from == call.to, &call.arcs))
        };
        // In a group, say where each call goes.
        let call_to = if single {
            "call".to_string()
        } else {
            format!("call to `{}`", to.name)
        };
        let message = if labelled.is_empty() {
            let call_to = if single {
                "recursive call".to_string()
            } else {
                call_to
            };
            format!("this {call_to} might not terminate: {what}")
        } else {
            format!("then this {call_to}: {what}")
        };
        diagnostic = diagnostic.with_label(call.span, message);
        labelled.push(c);
    }
    // A single call's label says it all; otherwise say what going round the
    // cycle does overall.
    let start = &members[calls[path[0]].from];
    if path.len() > 1 && !start.params.is_empty() {
        let round = if on_cycle.len() > 1 {
            let names: Vec<String> = path
                .iter()
                .map(|c| quoted(calls[*c].from))
                .chain([quoted(calls[path[0]].from)])
                .collect();
            format!("going round {}", names.join(" → "))
        } else {
            match (labelled.len(), path.len()) {
                (1, 2) => "making this call twice in a row".to_string(),
                (1, n) => format!("making this call {n} times in a row"),
                _ => "making these calls one after the other".to_string(),
            }
        };
        let overall: Vec<(usize, usize, Label)> = entries
            .iter()
            .enumerate()
            .filter_map(|(j, e)| e.map(|a| (a.from, j, a.label)))
            .collect();
        let note = if overall.iter().any(|(i, j, _)| shown(start, start, *i, *j)) {
            format!(
                "{round}, over and over: {}, so no argument keeps getting smaller",
                describe(start, start, true, &overall)
            )
        } else {
            format!("{round}, over and over, no argument is known to get smaller")
        };
        diagnostic = diagnostic.with_note(note);
    }
    if on_cycle.iter().any(|m| members[*m].returns_stream) {
        diagnostic = diagnostic.with_note(
            "a stream that refers to itself is built with `Stream.repeat`, `Stream.iterate` or \
             `Stream.unfold` (`Stream.repeat 1` is 1, 1, 1, …)",
        );
    }
    diagnostic
        .with_generic_note(
            "however the recursive calls are repeated, some argument must get smaller (a part of \
             a pattern-matched constructor); an argument passed on unchanged, or rebuilt from its \
             own pattern, is no smaller",
        )
        .with_generic_note(
            "non-terminating definitions are rejected unless they're partial: `{Partial}` in the \
             result type. A depth limit keeps it total and provable: an extra `fuel: Nat` \
             argument that decreases on each call, failing (or returning a default) when it runs \
             out",
        )
}

/// Says in words what a call (or a cycle of calls) from member `from` to
/// member `to` passes: for each argument position related to a parameter,
/// how. `same` if they're the same member.
fn describe(
    from: &MemberInfo,
    to: &MemberInfo,
    same: bool,
    arcs: &[(usize, usize, Label)],
) -> String {
    let parts: Vec<String> = arcs
        .iter()
        .filter(|(i, j, label)| *label == Label::Lt || shown(from, to, *i, *j))
        .map(|&(i, j, label)| {
            let (theirs, ours) = (position(&to.params, j), position(&from.params, i));
            if same {
                match (label, i == j) {
                    (Label::Lt, true) => format!("the {theirs} gets smaller"),
                    (Label::Le, true) => format!("the {theirs} stays the same"),
                    (Label::Lt, false) => format!("the {theirs} is smaller than the {ours} was"),
                    (Label::Le, false) => format!("the {theirs} is what the {ours} was"),
                }
            } else {
                let (callee, caller) = (to.name, from.name);
                match label {
                    Label::Lt => {
                        format!("`{callee}`'s {theirs} is smaller than `{caller}`'s {ours}")
                    }
                    Label::Le => format!("`{callee}`'s {theirs} is `{caller}`'s {ours}"),
                }
            }
        })
        .collect();
    if parts.is_empty() {
        "no argument is known to be smaller".to_string()
    } else {
        parts.join(", ")
    }
}

/// For a call in which no argument gets smaller, what it passes where the
/// callee matches, since those are the arguments that could have. `None` if
/// some argument gets smaller, or the callee matches on none.
fn not_smaller(
    g: &Ev,
    from: &MemberInfo,
    to: &MemberInfo,
    matched: &[bool],
    call: &Call,
) -> Option<String> {
    if call.arcs.iter().any(|(_, _, label)| *label == Label::Lt) {
        return None;
    }
    let same = call.from == call.to;
    let parts: Vec<String> = (0..to.params.len())
        .filter(|&j| matched[j])
        .map(|j| {
            // The argument as written, unless it's one a partial call
            // leaves to whatever the result is applied to.
            let arg = pretty::term_for_message(g, &call.names, &call.args[j]);
            let theirs = if arg == "_" {
                position(&to.params, j)
            } else {
                format!("{}, `{arg}`,", position(&to.params, j))
            };
            let arc = call.arcs.iter().find(|(_, to, _)| *to == j);
            match (arc, same) {
                (Some(&(i, _, _)), true) if i == j => format!("the {theirs} stays the same"),
                (Some(&(i, _, _)), true) => {
                    format!("the {theirs} is what the {} was", position(&from.params, i))
                }
                (Some(&(i, _, _)), false) => format!(
                    "`{}`'s {theirs} is `{}`'s {}",
                    to.name,
                    from.name,
                    position(&from.params, i)
                ),
                (None, true) => {
                    let (x, _) = &from.params[j];
                    if x.starts_with(['_', '%']) {
                        format!("the {theirs} isn't seen as smaller")
                    } else {
                        format!("the {theirs} isn't seen as smaller than `{x}`")
                    }
                }
                (None, false) => format!(
                    "`{}`'s {theirs} isn't seen as smaller than any of `{}`'s arguments",
                    to.name, from.name
                ),
            }
        })
        .collect();
    if parts.is_empty() {
        None
    } else {
        Some(parts.join("; "))
    }
}

/// How a message refers to parameter `i`.
fn position(params: &Params, i: usize) -> String {
    let (x, icit) = &params[i];
    if *icit == Icit::Explicit {
        let n = params[..i]
            .iter()
            .filter(|(_, icit)| *icit == Icit::Explicit)
            .count()
            + 1;
        format!("{} argument", ordinal(n))
    } else {
        format!("implicit argument `{x}`")
    }
}

/// Whether to mention an arc from parameter `i` of `from` to parameter `j`
/// of `to` that isn't strict: not if both are implicit (a type passed on
/// unchanged, say).
fn shown(from: &MemberInfo, to: &MemberInfo, i: usize, j: usize) -> bool {
    from.params[i].1 == Icit::Explicit || to.params[j].1 == Icit::Explicit
}

fn ordinal(n: usize) -> String {
    let suffix = match (n % 10, n % 100) {
        (1, x) if x != 11 => "st",
        (2, x) if x != 12 => "nd",
        (3, x) if x != 13 => "rd",
        _ => "th",
    };
    format!("{n}{suffix}")
}

/// Running out while deciding the calls: there's no answer, so no member
/// is accepted.
fn inconclusive(e: ResourceError, members: &[MemberInfo]) -> Diagnostic {
    let names: Vec<String> = members.iter().map(|m| format!("`{}`", m.name)).collect();
    let (checking, accepted) = match &names[..] {
        [name] => (
            format!("while checking that {name} terminates"),
            format!("{name} isn't accepted"),
        ),
        _ => {
            let all = names.join(", ");
            (
                format!("while checking that {all} terminate"),
                format!("none of {all} is accepted"),
            )
        }
    };
    Diagnostic::from(e)
        .with_label(members[0].span, checking)
        .with_note(format!(
            "the termination check is inconclusive, so {accepted}"
        ))
}

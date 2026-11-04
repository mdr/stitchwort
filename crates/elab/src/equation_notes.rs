//! What the compiler says about generated equations
//! (docs/proposals/function-equations.md §3.4, §7.3, §10): the error for an
//! equation name that no longer exists, and the note on a `rewrite` with an
//! arm equation whose left side the goal has already computed. The
//! equations themselves are made by `equations.rs`.

use crate::Global;
use stitchwort_core::{DefId, Term};
use stitchwort_syntax::Diagnostic;
use stitchwort_syntax::ast::{self, Expr};

use crate::check::Ctx;

/// `E-UNKNOWN-NAME` for `f.eq9`, where `f` is a definition with no such
/// equation: arms are numbered, so adding or removing one renumbers the ones
/// after it, and proofs that name them stop checking (§10). The note says
/// which equations `f` has and where to see them.
pub(crate) fn unknown_equation(cx: &Ctx, name: &ast::Name) -> Option<Diagnostic> {
    let e = cx.e;
    let (owner, suffix) = crate::equations::reserved_suffix(&name.text)?;
    // A local variable called `f` is dot notation's, not a name.
    if cx.lookup(owner).is_some() || matches!(cx.local(owner), Ok(Some(_))) {
        return None;
    }
    let Some((Global::Def(f), _)) = e.named(owner) else {
        return None;
    };
    let def = e.kernel.def(*f);
    if def.theorem() || def.instance() || e.named(&name.text).is_some() {
        return None;
    }
    // `f.induct` of a definition that doesn't call itself.
    if suffix == "induct" {
        let written = def.name();
        return Some(
            Diagnostic::error("E-UNKNOWN-NAME", format!("unknown name `{written}.induct`"))
                .with_label(name.span, "no such induction principle")
                .with_note(format!(
                    "`{written}` doesn't call itself, so it has no `{written}.induct`: a proof \
                     about it splits as it does, with its equations (`stitchwort doc {written}` \
                     lists them)"
                )),
        );
    }
    // The arm numbers there are: `f.eq1`, `f.eq2`, … (an `or` or a branch
    // below an arm has its arm's number).
    let prefix = format!("{}.eq", def.path());
    let mut arms: Vec<usize> = (0..e.kernel.env.defs().len())
        .map(stitchwort_core::DefId)
        .filter_map(|id| {
            let d = e.kernel.def(id);
            let rest = d.path().strip_prefix(&prefix)?;
            let number = rest.split('.').next()?;
            if d.theorem() {
                number.parse().ok()
            } else {
                None
            }
        })
        .collect();
    arms.sort_unstable();
    arms.dedup();
    let written = def.name();
    let have = match (arms.first(), arms.last()) {
        (Some(first), Some(last)) if first == last => {
            format!("`{written}` has the equation `{written}.eq{first}`")
        }
        (Some(first), Some(last)) => {
            format!("`{written}` has equations `{written}.eq{first}` to `{written}.eq{last}`")
        }
        _ => format!("`{written}` has no equations (it has no arms, or none could be stated)"),
    };
    Some(
        Diagnostic::error(
            "E-UNKNOWN-NAME",
            format!("unknown name `{written}.{suffix}`"),
        )
        .with_label(name.span, "no such equation")
        .with_note(format!(
            "{have}: they are numbered by arm, so adding or removing an arm renumbers the \
                 ones after it"
        ))
        .with_note(format!(
            "`stitchwort doc {written}` lists the equations of `{written}` and which \
                 weren't generated"
        )),
    )
}

/// The name of the generated equation a `rewrite` rule's proof starts with:
/// `f.eq2` (written as one name, or `f` and a field), applied or not.
pub(crate) fn rule_equation(proof: &Expr) -> Option<String> {
    match proof {
        Expr::App(head, _) | Expr::Bracketed(head, _) => rule_equation(head),
        Expr::Var(n) if crate::equations::is_equation_name(&n.text) => Some(n.text.clone()),
        Expr::Field(inner, field) => match &**inner {
            Expr::Var(owner)
                if crate::equations::is_equation_name(&format!("f.{}", field.text)) =>
            {
                Some(format!("{}.{}", owner.text, field.text))
            }
            _ => None,
        },
        _ => None,
    }
}

/// The note for an `E-REWRITE-NOTHING` whose rule is the generated equation
/// `equation` (§7.3): a call of an arm equation's function that computes in
/// the goal is already its computed form, so there is nothing to replace.
pub(crate) fn computed_equation_note(equation: &str) -> String {
    let owner = crate::equations::reserved_suffix(equation).map_or(equation, |(o, _)| o);
    format!(
        "`{equation}` is a generated equation for an arm of `{owner}`. A call that computes in \
         the goal (its arguments are constructors) is already its computed form, as the goal \
         shows above, so there is nothing for the equation to replace. Arm equations are for \
         calls that are stuck (on a variable, or in a `decreasing` or `opaque` definition): \
         `stitchwort doc {owner}` marks those `[stuck]`"
    )
}

/// The note for an `E-MATCH-MOTIVE`, `E-REWRITE-MOTIVE` or `E-REFL` whose
/// terms mention a lifted `match`'s helper (§3.4): the generated branch
/// equations that state its steps (`firstBig.eq2.true`), which is what
/// stepping through it by hand fails to do (§1.2). `None` if no helper is
/// mentioned or none of its branches has an equation.
pub(crate) fn branch_note(e: &crate::Elaborator, terms: &[&Term]) -> Option<String> {
    let g = &e.ev();
    let mut helpers: Vec<DefId> = Vec::new();
    for t in terms {
        for (s, _) in t.subterms() {
            if let Term::Def(id) = s
                && g.def(*id).name().contains(".%match")
                && !helpers.contains(id)
            {
                helpers.push(*id);
            }
        }
    }
    let first = *helpers.first()?;
    // A branch through the `match` uses the helper's equation for its
    // alternative: the hidden lemma `f.%match1.eq2`, or that equation
    // inline, `(proof : … → f.%match1 … = …)`. (Its statement may name the
    // helper without stepping through it: `(match …) || …`.)
    let lemmas: Vec<String> = helpers
        .iter()
        .map(|h| format!("{}.eq", g.def(*h).name()))
        .collect();
    let is_lemma = |id: &DefId| {
        lemmas
            .iter()
            .any(|n| g.def(*id).name().starts_with(n.as_str()))
    };
    let states_helper = |ty: &Term| {
        let mut t = ty.strip_loc();
        while let Term::Pi(_, _, _, cod) = t {
            t = cod.strip_loc();
        }
        matches!(t, Term::Eq(_, lhs, _)
            if matches!(lhs.spine().0, Term::Def(id) if helpers.contains(id)))
    };
    let mut found: Vec<String> = Vec::new();
    for i in 0..g.env.defs().len() {
        let d = g.def(DefId(i));
        if !d.theorem() || d.name().contains('%') || !crate::equations::is_equation_name(d.name()) {
            continue;
        }
        let Some(body) = d.body() else { continue };
        if body.subterms().any(|(s, _)| match s {
            Term::Def(id) => is_lemma(id),
            Term::Ann(_, ty) => states_helper(ty),
            _ => false,
        }) {
            found.push(format!("`{}`", d.name()));
        }
    }
    let owner = g.def(first).name().rsplit_once(".%match")?.0.to_string();
    let listed = match found.len() {
        0 => return None,
        1..=4 => found.join(", "),
        n => format!("{}, … ({n} in all)", found[..3].join(", ")),
    };
    Some(format!(
        "the `match` inside `{owner}` has generated equations, one for each way through it: \
         {listed}, each under the hypothesis its branch is taken under; `stitchwort doc \
         {owner}` lists them"
    ))
}

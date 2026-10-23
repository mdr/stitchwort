//! Erasure decisions shared by the JS backend (`crates/js`) and the
//! runtime's lowering (D389): which parameters of a definition are erased,
//! whether its result is, which definitions a program uses, and the shapes
//! both recognise in checked terms. What's erased is described in
//! docs/core.md, "Erasure and JS extraction".

use stitchwort_core::check::telescope;
use stitchwort_core::partial::Primitive;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{Head, force};
use stitchwort_core::{DefId, Globals, Term, Value};
use stitchwort_syntax::Diagnostic;

/// What erasure decides about a definition from its type.
pub struct DefShape {
    /// For each parameter of its type, whether it's erased (a proof or a
    /// type former).
    pub params: Vec<bool>,
    /// How many leading parameters a call passes before the definition runs:
    /// its arity (the lambdas of its body), or for one of `Delay`'s
    /// constants, which have no body, all of its parameters.
    pub mask_len: usize,
    /// Whether its result is erased: a proof or a type.
    pub result_erased: bool,
    /// Whether its result is a partial computation (`Delay op res a`).
    pub partial: bool,
}

impl DefShape {
    /// Which of the leading parameters a call passes are erased.
    pub fn mask(&self) -> &[bool] {
        &self.params[..self.mask_len.min(self.params.len())]
    }

    /// How many of [`DefShape::mask`] are passed at run time.
    pub fn runtime_arity(&self) -> usize {
        self.mask().iter().filter(|erased| !**erased).count()
    }
}

/// [`DefShape`] for definition `id`. With `primitives_whole`, one of
/// `Delay`'s constants takes all of its parameters (it has no body, so no
/// arity): for backends that build `Delay` values rather than erasing them.
pub fn def_shape(g: &Globals, id: DefId, primitives_whole: bool) -> Result<DefShape, Diagnostic> {
    let def = g.def(id);
    let tel = telescope(g, &def.ty_value, def.span)?;
    let partial = match (
        force(g, tel.result)?,
        g.builtins.primitive_id(Primitive::Delay),
    ) {
        (Value::Neutral(Head::Def(d), spine), Some(delay)) => d == delay && spine.len() == 3,
        _ => false,
    };
    let params: Vec<bool> = tel.params.iter().map(|(_, _, erased)| *erased).collect();
    // A float primitive has no body either, and no parameter to erase.
    let mask_len = if (primitives_whole && g.builtins.primitive(id).is_some())
        || g.builtins.float_primitive(id).is_some()
    {
        params.len()
    } else {
        def.arity
    };
    Ok(DefShape {
        params,
        mask_len,
        result_erased: tel.result_erased,
        partial,
    })
}

/// Which definitions the given ones use, directly or indirectly, indexed by
/// [`DefId`]. What an `opaque` definition's body uses doesn't count: an
/// erased one (a proof or a type) or a natively implemented one.
pub fn reachable(
    g: &Globals,
    roots: impl IntoIterator<Item = DefId>,
    opaque: impl Fn(DefId) -> bool,
) -> Vec<bool> {
    fn visit(term: &Term, found: &mut Vec<DefId>) {
        found.extend(term.subterms().filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        }));
    }
    let mut used = vec![false; g.defs.len()];
    let mut stack: Vec<DefId> = roots.into_iter().collect();
    while let Some(id) = stack.pop() {
        if std::mem::replace(&mut used[id.0], true) {
            continue;
        }
        let def = g.def(id);
        if let Some(body) = def.run_body()
            && !opaque(id)
        {
            visit(body, &mut stack);
        }
        for validator in &def.validators {
            visit(&validator.decision, &mut stack);
        }
    }
    used
}

/// The definitions a term refers to, in order: the roots of a program
/// whose entry is that term.
pub fn defs_in(term: &Term) -> Vec<DefId> {
    term.subterms()
        .filter_map(|(t, _)| match t {
            Term::Def(id) => Some(*id),
            _ => None,
        })
        .collect()
}

/// Whether `y => body` is `y => Done y`, the continuation the elaborator
/// writes for an operation or a recursion request, which a runner
/// recognises to run a tail request in constant space (as
/// `stitchwort_core::step` does).
pub fn is_done_continuation(g: &Globals, body: &Term) -> bool {
    let mut body = body;
    while let Term::Loc(_, t) | Term::Ann(t, _) = body {
        body = t;
    }
    matches!(body, Term::Ctor(d, 0, fields)
        if Some(*d) == g.registry.data(Builtin::Comp)
            && matches!(&fields[..], [field] if matches!(field.strip_loc(), Term::Var(0))))
}

/// The characters of a list of `Char`s written out in full (like a text
/// literal's), if it is one: cons cells of literal characters, ending in
/// `Nil` or a compact list. A loop, since a long literal nests deeply.
pub fn text_literal(chars: &Term) -> Option<String> {
    let mut text = String::new();
    let mut list = chars.strip_loc();
    loop {
        match list {
            Term::Chars(rest) => {
                text.extend(rest.as_slice());
                return Some(text);
            }
            Term::Ctor(_, 0, args) if args.is_empty() => return Some(text),
            Term::Ctor(_, 1, args) if args.len() == 2 => {
                let Term::Ctor(_, 0, fields) = args[0].strip_loc() else {
                    return None;
                };
                let Term::Nat(code) = fields.first()?.strip_loc() else {
                    return None;
                };
                text.push(u32::try_from(&**code).ok().and_then(char::from_u32)?);
                list = args[1].strip_loc();
            }
            _ => return None,
        }
    }
}

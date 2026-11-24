//! Which theorems an interface pass leaves the proofs of to the proof job
//! (docs/proposals/parallel-checking-stage-3.md §3, D3735): the deferral
//! rule. It is decided from the source alone, before any signature is
//! elaborated, so it is the same in every session, and so that nothing the
//! elaborator would do to a theorem between its signature and its proof
//! (a mark the kernel takes only on a pending definition) can be missed:
//! a theorem with such a mark in its source is elaborated.

use stitchwort_syntax::ast::Decl;

use crate::Elaborator;

impl Elaborator {
    /// Whether the interface pass under way leaves out the proofs of
    /// `members`, a component of the namespace's declarations: each is then
    /// settled as a stated theorem whose proof hasn't been checked
    /// (`check::leave_stated`) where the full check would elaborate its
    /// proof. All of these must hold:
    ///
    /// 1. This is the interface pass of a project namespace
    ///    ([`Elaborator::set_interface_pass`]), not the prelude or a library
    ///    file loaded inside it.
    /// 2. Every member is a `theorem` with none of the marks a stated
    ///    theorem can't carry, as written: not an instance, a synonym or an
    ///    export, not `opaque`, no `unfolding` list, no parameter default,
    ///    no attribute but `@[reading]` and the `@[walk…]` family (which
    ///    read only the statement), and no syntax error. (`fold`, `tailrec`
    ///    and run bodies come only with definitions.)
    /// 3. No member's proof holds a local `def` or `theorem`, which can be
    ///    named from outside it today (`t.go`), so it is part of the
    ///    interface (rule 3 of the design; D3736 makes them private to the
    ///    proof, SW-4762, after which this rule goes).
    /// 4. The component holds only theorems: a theorem grouped with a
    ///    computing definition shares its hash, which covers its proof.
    ///
    /// A recursive, mutual or `decreasing` component is deferred like a
    /// lone theorem: its termination check is part of its proof, and with
    /// every proof left out the digests of `tools/fmt` and `aoc` match the
    /// full check's (SW-4757, SW-4761). A `decreasing` theorem then declares
    /// no `%step` or `%go`, which the digest leaves out anyway (parallel-
    /// checking.md 11.4).
    pub(crate) fn defers_proofs(&self, members: &[(usize, &Decl, &[Decl])]) -> bool {
        let Some(ns) = self.unit.module.namespace.as_deref() else {
            return false;
        };
        if !self.interface_pass_of(ns)
            || self.unit.loading_prelude
            || !self.library_stack_is_empty()
        {
            return false;
        }
        members.iter().all(|(_, signature, equations)| {
            plain_theorem(signature) && !crate::module::has_local_defs(equations)
        })
    }
}

/// Rule 2 of [`Elaborator::defers_proofs`].
fn plain_theorem(signature: &Decl) -> bool {
    let Decl::Signature {
        theorem,
        export,
        synonym,
        instance,
        opaque,
        unfolding,
        defaults,
        attrs,
        syntax_error,
        ..
    } = signature
    else {
        return false;
    };
    let statement_only = |name: &str| {
        name == crate::attributes::READING
            || [
                crate::walk::WALK,
                crate::walk::WALK_BIND,
                crate::walk::WALK_DONE,
                crate::walk::WALK_WEAKEN,
            ]
            .contains(&name)
    };
    *theorem
        && !*export
        && !*synonym
        && !*instance
        && !*opaque
        && unfolding.is_empty()
        && defaults.iter().all(Option::is_none)
        && attrs.iter().all(|a| statement_only(&a.name.text))
        && syntax_error.is_none()
}

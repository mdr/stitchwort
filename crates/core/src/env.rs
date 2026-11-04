//! The kernel's environment: the declarations admitted so far.

use crate::globals::{Data, Def};
use crate::native::{Builtins, BuiltinsMark};
use crate::registry::Registry;
use crate::term::{DataId, DefId};

/// What the kernel and the evaluator read of the declarations admitted so
/// far (docs/proposals/globals-split.md §4): the definitions and data types,
/// the built-ins bound to them, and the prelude identities.
///
/// Every field is private to this crate. Outside it the environment is
/// read through the methods below; the only writers are the kernel's own
/// functions (`check.rs`, `native.rs`, `registry.rs`, ...), which reach the
/// fields through the `pub(crate)` `*_mut` methods. Nothing outside
/// `stitchwort-core` can write a declaration's type, body or state.
#[derive(Default)]
pub struct Env {
    defs: Vec<Def>,
    datas: Vec<Data>,
    builtins: Builtins,
    registry: Registry,
}

impl Env {
    /// Every definition, by [`DefId`].
    pub fn defs(&self) -> &[Def] {
        &self.defs
    }

    /// Every data type, by [`DataId`].
    pub fn datas(&self) -> &[Data] {
        &self.datas
    }

    pub fn def(&self, id: DefId) -> &Def {
        &self.defs[id.0]
    }

    pub fn data(&self, id: DataId) -> &Data {
        &self.datas[id.0]
    }

    /// `Nat` and the definitions with native implementations.
    pub fn builtins(&self) -> &Builtins {
        &self.builtins
    }

    /// The prelude declarations the compiler refers to, by identity.
    pub fn registry(&self) -> &Registry {
        &self.registry
    }

    /// Switches the number natives off (for tests and tools that compare
    /// them with their definitions): a setting, not a declaration.
    pub fn set_disable_natives(&mut self, off: bool) {
        self.builtins.disable_natives = off;
    }

    /// Elaborates text literals as constructors, not compactly (a setting).
    pub fn set_disable_compact_text(&mut self, off: bool) {
        self.builtins.disable_compact_text = off;
    }

    /// Switches the float natives off while the number natives stay on (a
    /// setting).
    pub fn set_disable_float_natives(&mut self, off: bool) {
        self.builtins.disable_float_natives = off;
    }

    /// Lets the float natives fire outside a running program, for the float
    /// gate only (a setting; see [`Builtins::float_natives_outside_runs`]).
    pub fn set_float_natives_outside_runs(&mut self, on: bool) {
        self.builtins.float_natives_outside_runs = on;
    }

    /// Forgets the built-in `b`'s binding, as if the prelude didn't declare
    /// it: for a test of what depends on the registry.
    #[cfg(feature = "test-bypass")]
    pub fn forget_builtin_for_tests(&mut self, b: crate::registry::Builtin) {
        self.registry.forget_for_test(b);
    }

    /// Pushes a copy of definition `from` named `name` with `body`, without
    /// admission, for tests that build deliberately broken states.
    #[cfg(feature = "test-bypass")]
    pub fn push_copy_unchecked_for_tests(
        &mut self,
        from: DefId,
        name: crate::term::Name,
        body: Option<std::rc::Rc<crate::term::Term>>,
    ) {
        let mut def = self.defs[from.0].clone();
        def.name = name;
        def.export = false;
        def.validators = Vec::new();
        def.body = body;
        self.defs.push(def);
    }

    /// Mutable access to definition `id`, for tests that build deliberately
    /// broken states through [`Def`]'s `*_unchecked_for_tests` setters.
    #[cfg(feature = "test-bypass")]
    pub fn def_mut_for_tests(&mut self, id: DefId) -> &mut Def {
        &mut self.defs[id.0]
    }

    /// As [`Env::def_mut_for_tests`], for a data type.
    #[cfg(feature = "test-bypass")]
    pub fn data_mut_for_tests(&mut self, id: DataId) -> &mut Data {
        &mut self.datas[id.0]
    }

    /// Binds the compact-text representation without checking the
    /// declarations it names, for unit tests of unification.
    #[cfg(feature = "test-bypass")]
    pub fn set_text_unchecked_for_tests(&mut self, text: crate::chars::CompactText) {
        self.builtins.text = Some(text);
    }

    pub(crate) fn defs_mut(&mut self) -> &mut Vec<Def> {
        &mut self.defs
    }

    pub(crate) fn datas_mut(&mut self) -> &mut Vec<Data> {
        &mut self.datas
    }

    pub(crate) fn builtins_mut(&mut self) -> &mut Builtins {
        &mut self.builtins
    }

    pub(crate) fn registry_mut(&mut self) -> &mut Registry {
        &mut self.registry
    }

    /// Removes the definitions from `defs` on and the data types from
    /// `datas` on, with the registry entries bound to them.
    pub(crate) fn truncate(&mut self, defs: usize, datas: usize) {
        self.defs.truncate(defs);
        self.datas.truncate(datas);
        self.registry.forget_from(defs, datas);
    }

    /// What [`crate::Globals::rewind`] does to the environment: lengths and
    /// bindings only.
    pub(crate) fn rewind(&mut self, defs: usize, datas: usize, builtins: &BuiltinsMark) {
        self.truncate(defs, datas);
        self.builtins.rewind(builtins, defs);
    }
}

use super::*;

pub(crate) struct Gen<'g> {
    pub(crate) g: &'g View<'g>,
    /// The prelude's `Nat`, if the `bigint` representation applies
    /// ([`nat_data`]).
    pub(crate) nat: Option<DataId>,
    /// The prelude's `Text`, if it's a JS string in generated code
    /// ([`Options::native_text`], [`text_data`]).
    pub(crate) text: Option<DataId>,
    /// The prelude's text operations with native JS, and which.
    pub(crate) text_natives: HashMap<DefId, TextNative>,
    /// The prelude's `Int`, if it's a `bigint` in generated code
    /// ([`Options::native_int`], [`bind_int`]).
    pub(crate) int: Option<DataId>,
    /// The prelude's integer operations with native JS, and which.
    pub(crate) int_natives: HashMap<DefId, IntNative>,
    /// The library's `Float`, if it's loaded: then a `Float` is a JS
    /// `number` (docs/proposals/float.md §3.5).
    pub(crate) float: Option<DataId>,
    /// The `Float` operations with native JS, and which.
    pub(crate) float_natives: HashMap<DefId, FloatPrim>,
    /// The library's `Array`, if it's loaded: then an array is a version
    /// array ([`VERSION_ARRAYS`]; docs/proposals/arrays.md §4.3).
    pub(crate) array: Option<DataId>,
    /// Its operations with native JS: all of them, or the program is
    /// refused ([`stitchwort_rt::natives::ArrayBinding::refusal`]).
    pub(crate) array_natives: HashMap<DefId, ArrayNative>,
    /// Per definition, computed on first use ([`Gen::try_info`]).
    pub(crate) infos: Vec<OnceCell<DefInfo>>,
    /// Each data type at the boundary's fields' boundaries, with the type's
    /// parameters as [`Boundary::Param`]. Read here, where only strings can be
    /// built, but computed once before, where a resource refusal can be
    /// reported (SW-3960).
    pub(crate) fields: HashMap<DataId, Vec<Vec<(String, Boundary)>>>,
    /// The prelude's `ifThenElse`, which `if` becomes.
    pub(crate) if_then_else: Option<DefId>,
    /// `Decidable.elim`, which `if h: p then a else b` becomes.
    pub(crate) elim_dec: Option<DefId>,
    /// `Bool.not`, whose calls are the opposite test.
    pub(crate) bool_not: Option<DefId>,
    /// The prelude's `Decidable` type: a definition whose result is one
    /// decides a proposition ([`Gen::unfolds_decision`]).
    pub(crate) decidable: Option<DataId>,
    /// `Ord.compare` and `Ord.fromCompare`: a comparison through an instance
    /// the code names is a call of its `compare` ([`Gen::known_compare`]).
    pub(crate) ord_compare: Option<DefId>,
    pub(crate) ord_from_compare: Option<DefId>,
    /// `Nat.add`, whose calls in tail position a loop can add up as it goes
    /// ([`SelfCall::add`]), with the `bigint` representation of `Nat`.
    pub(crate) nat_add: Option<DefId>,
    /// `List.append`, whose calls in tail position a loop that builds cells
    /// can copy its first argument for ([`SelfCall::cons`]).
    pub(crate) list_append: Option<DefId>,
    /// The effect runtime, which replaces the library functions that take a
    /// computation apart (docs/proposals/effect-runtime.md §9), if the
    /// core is loaded.
    pub(crate) effect: Option<effect::Effect>,
    /// For `stitchwort run --js` ([`run`]): a `Delay` is a real value that
    /// the runner steps, rather than the erased token, so partial
    /// definitions are generated, and `Delay`'s constants build
    /// `StitchwortDelay` objects.
    pub(crate) run_delay: bool,
    /// While a loop's body is being generated ([`Gen::self_tail_loop`]): the
    /// variables that stand for a call to the definition itself, which was
    /// an argument to a helper that's been inlined ([`Gen::tail`]), by
    /// level, with what the next turn of the loop would be passed.
    pub(crate) holes: RefCell<Vec<(usize, Passed)>>,
    /// While a loop's body is being generated: the variables that stand for
    /// a function whose body is a call to the definition itself, which was
    /// an argument to a helper that's been inlined: the `%rec` of a
    /// definition by `decreasing` (crates/elab/src/decreasing.rs), whose
    /// runtime body is `f.%step x (y c p => f y c) c`.
    pub(crate) fn_holes: RefCell<Vec<FnHole>>,
    /// Whether such a variable was used any way but in tail position, or
    /// as a field of a constructor in tail position, where it can't be
    /// compiled.
    pub(crate) hole_misused: Cell<bool>,
    /// The fast path's generated codecs ([`fast`]).
    pub(crate) fast: RefCell<fast::Fast>,
    /// Decides which calls are at the empty row, and makes the variants
    /// (docs/proposals/effect-polymorphism.md, design E).
    pub(crate) spec: Specialiser<'g>,
    /// Per definition: whether it's used as it is, and whether through its
    /// empty-row variant ([`Gen::set_reach`]).
    pub(crate) used: RefCell<Vec<bool>>,
    pub(crate) empty: RefCell<Vec<bool>>,
    /// Per definition, its empty-row variant's [`DefInfo`].
    pub(crate) empty_infos: Vec<OnceCell<DefInfo>>,
    /// Recognises closed signature maps, which are built once
    /// ([`stitchwort_rt::hoist`], stage 4f).
    pub(crate) sig_maps: Option<SigMaps>,
    /// The closed maps found so far: `sigmap$i` is built by the `i`th.
    pub(crate) hoisted: RefCell<Vec<String>>,
    /// Whether a map's own code is being generated (a map inside it is
    /// built with it, not separately).
    pub(crate) hoisting: Cell<bool>,
    /// The curried forms of uncurried definitions used as values, by name
    /// (`f$c`, built at its first use and kept in a module variable).
    pub(crate) curried: RefCell<Vec<String>>,
    /// The definitions generated so far, by JS name ([`Gen::share`]).
    pub(crate) emitted: RefCell<HashMap<String, DefId>>,
    /// The right-hand sides of the values generated so far, each with the
    /// name of the first value that has it.
    pub(crate) values: RefCell<HashMap<String, String>>,
    /// Definitions that are, at run time, one generated before them: with
    /// that one's JS name, which every use names instead ([`Gen::share`]).
    pub(crate) aliases: RefCell<HashMap<DefId, String>>,
    /// [`Gen::forwarder`]'s answers, by definition.
    pub(crate) forwarders: RefCell<HashMap<DefId, Option<Forward>>>,
}

/// What the generator decides about a definition from its type.
pub(crate) struct DefInfo {
    /// Whether it's a proof or a type.
    pub(crate) result_erased: bool,
    /// Which of its leading parameters (up to its arity) are erased.
    pub(crate) mask: Vec<bool>,
    /// How it's compiled and called, decided once and used at every site.
    pub(crate) convention: Convention,
    /// For a [`Convention::Function`] with two or more runtime parameters:
    /// its JS takes them all in one call, `f(a, b)`, rather than one at a
    /// time (D1173). A call with all of them is one call; a partial
    /// application, or a use as a value, is a closure that takes the rest
    /// one at a time, as every function value does.
    pub(crate) uncurried: bool,
    /// For a definition whose result is a `Delay` (a partial function, or one
    /// of `Delay`'s constants): which of its parameters are erased. It's
    /// never generated: a call to it with all its arguments is the token
    /// `delayed`, and with fewer, a function returning the token.
    pub(crate) delay: Option<Vec<bool>>,
}

/// How a definition is compiled, and so how every site uses it: its
/// declaration, references to it, applications, first-class uses and export
/// wrappers (docs/proposals/mutual-recursion.md §8.6).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Convention {
    /// A proof or a type: nothing is generated, and it's `undefined`.
    Erased,
    /// No runtime parameters, not a case tree and not in a group: `const f =
    /// …;`, computed when the module loads, used as `f`.
    Value,
    /// No runtime parameters, and either a case tree (like `absurd`, whose
    /// case is on an erased proof, so it mustn't run until it's used) or a
    /// member of a group of definitions that call each other (which mustn't
    /// call a sibling while the module loads, before the sibling is
    /// defined): `const f = () => …;`, used as `f()`.
    Thunk,
    /// Runtime parameters: `const f = (v0) => …;`, used as `f`, applied as
    /// `f(a)`.
    Function,
}

/// The definition being generated, for turning calls to itself in tail
/// position into another turn of a loop. JS engines don't eliminate tail
/// calls, so otherwise each would use a stack frame.
/// What a turn of a loop is passed: parameter levels and JS values.
pub(crate) type Passed = Vec<(usize, String)>;

/// A variable that stands for `x1 … xk => body`, where `body` is a call to
/// the definition whose loop is being generated ([`Gen::fn_holes`]).
pub(crate) struct FnHole {
    /// The variable's level.
    pub(crate) level: usize,
    /// `k`, and the parameters' names.
    pub(crate) params: Vec<stitchwort_core::Name>,
    /// The body, under the `k` parameters, in an environment of `site`
    /// variables.
    pub(crate) body: Term,
    pub(crate) site: usize,
}

/// The cells a constructor makes (`Gen::cons_cells`): the outermost, the
/// innermost, its field that takes the rest, and what the next turn is passed.
pub(crate) type Cells = (String, String, String, Passed);

pub(crate) struct SelfCall {
    pub(crate) id: DefId,
    /// Whether the loop is the definition's empty-row variant's.
    pub(crate) variant: bool,
    /// Whether any call was turned into a loop.
    pub(crate) used: Cell<bool>,
    /// Whether a call in a constructor's field, in tail position, is a turn
    /// of the loop too (tail recursion modulo constructor): the loop builds
    /// the result a cell at a time.
    pub(crate) cons: bool,
    /// Whether any was.
    pub(crate) cons_used: Cell<bool>,
    /// Whether a call in tail position under `Succ` or `Nat.add` is a turn
    /// of the loop too (tail recursion modulo addition): the loop keeps the
    /// sum of what it was to be added to, `a$`, and adds it to the result.
    /// `List.length`'s `Succ (List.length xs)`.
    pub(crate) add: bool,
    /// Whether any was.
    pub(crate) add_used: Cell<bool>,
    /// Whether to inline a helper that a call to the definition is an
    /// argument of, in tail position.
    pub(crate) inline: bool,
    /// How many helpers are being inlined, and a counter for names.
    pub(crate) inlining: Cell<usize>,
    pub(crate) fresh: Cell<usize>,
    /// The definitions being inlined, innermost last: one isn't inlined
    /// into itself.
    pub(crate) inlined: RefCell<Vec<DefId>>,
}

impl SelfCall {
    pub(crate) fn new(id: DefId, variant: bool, cons: bool, add: bool, inline: bool) -> Self {
        SelfCall {
            id,
            variant,
            used: Cell::new(false),
            cons,
            cons_used: Cell::new(false),
            add,
            add_used: Cell::new(false),
            inline,
            inlining: Cell::new(0),
            fresh: Cell::new(0),
            inlined: RefCell::new(Vec::new()),
        }
    }

    pub(crate) fn fresh(&self) -> usize {
        self.fresh.set(self.fresh.get() + 1);
        self.fresh.get()
    }
}

impl<'g> Gen<'g> {
    pub(crate) fn new(
        g: &'g View<'g>,
        options: Options,
        fields: HashMap<DataId, Vec<Vec<(String, Boundary)>>>,
    ) -> Result<Self, Diagnostic> {
        let Representation {
            nat,
            text,
            mut text_natives,
            int,
            int_natives,
            float,
            float_natives,
        } = Representation::new(g, options.native_text, options.native_int)
            .map_err(Diagnostic::from)?;
        text_natives.retain(|_, op| op.in_js());
        // All or nothing, and loud, as on the machine: an array without its
        // natives would run each O(1) operation as an O(n) one on its list.
        let arrays = bind_array(g).map_err(Diagnostic::from)?;
        if let Some(why) = arrays.refusal() {
            return Err(Diagnostic::error("E-BUILTIN", why));
        }
        let (array, array_natives) = match arrays.applies() {
            Some((d, natives)) => (Some(d), natives),
            None => (None, HashMap::default()),
        };
        Ok(Gen {
            g,
            nat,
            text,
            text_natives,
            int,
            int_natives,
            float,
            float_natives,
            array,
            array_natives,
            infos: g.env.defs().iter().map(|_| OnceCell::new()).collect(),
            fields,
            if_then_else: g.env.registry().def(Builtin::IfThenElse),
            elim_dec: g.env.registry().def(Builtin::ElimDec),
            bool_not: g.env.registry().def(Builtin::BoolNot),
            decidable: g.env.registry().data(Builtin::Decidable),
            ord_compare: g.env.registry().def(Builtin::OrdCompare),
            ord_from_compare: g.env.registry().def(Builtin::OrdFromCompare),
            nat_add: nat.and(g.env.registry().def(Builtin::Add)),
            list_append: g.env.registry().def(Builtin::Append),
            effect: effect::Effect::new(g, options.effect_counters),
            run_delay: false,
            holes: RefCell::new(Vec::new()),
            fn_holes: RefCell::new(Vec::new()),
            hole_misused: Cell::new(false),
            fast: RefCell::default(),
            spec: Specialiser::new(g),
            used: RefCell::new(vec![true; g.env.defs().len()]),
            empty: RefCell::new(vec![false; g.env.defs().len()]),
            empty_infos: g.env.defs().iter().map(|_| OnceCell::new()).collect(),
            sig_maps: SigMaps::new(g),
            hoisted: RefCell::new(Vec::new()),
            hoisting: Cell::new(false),
            curried: RefCell::new(Vec::new()),
            emitted: RefCell::default(),
            values: RefCell::default(),
            aliases: RefCell::default(),
            forwarders: RefCell::default(),
        })
    }

    /// Data type `d`'s fields' boundaries, with its parameters left as
    /// [`Boundary::Param`], as they were computed before generation.
    pub(crate) fn generic_fields(&self, d: DataId) -> &[Vec<(String, Boundary)>] {
        self.fields
            .get(&d)
            .expect("every data type at the boundary has its fields")
    }

    /// [`field_boundaries`] for the given arguments, from the computed map.
    pub(crate) fn field_boundaries(
        &self,
        d: DataId,
        args: &[Boundary],
    ) -> Vec<Vec<(String, Boundary)>> {
        self.generic_fields(d)
            .iter()
            .map(|fields| {
                fields
                    .iter()
                    .map(|(name, b)| (name.clone(), b.instantiate(args)))
                    .collect()
            })
            .collect()
    }

    /// What the program uses: the definitions `roots` and the terms
    /// `entries` refer to, directly or indirectly, with calls at the empty
    /// row using the callee's variant ([`specialise::reachable`]). Recorded
    /// for [`Gen::def`], and returned as the definitions to generate, by
    /// [`dependency_order`]. With `delay`, a definition whose result is a
    /// partial computation is opaque, and isn't generated.
    pub(crate) fn set_reach(
        &self,
        roots: impl IntoIterator<Item = DefId>,
        entries: &[&Term],
        delay: bool,
    ) -> Result<Vec<DefId>, Diagnostic> {
        let g = self.g;
        let failure = RefCell::new(None);
        // An inlined call's body may fail to unfold with the stack or a
        // limit; that's the generator's error, reported after reachability.
        let inline_failure = RefCell::new(None);
        let reach = specialise::reachable_inlining(
            &self.spec,
            roots,
            entries,
            |id| match self.try_info(id) {
                Ok(info) => {
                    info.result_erased || self.is_native(id) || (delay && info.delay.is_some())
                }
                Err(e) => {
                    failure.borrow_mut().get_or_insert(e);
                    true
                }
            },
            |id, args| match self.inlined(id, args) {
                Ok(inlined) => inlined,
                Err(e) => {
                    inline_failure.borrow_mut().get_or_insert(e);
                    specialise::Inlined::No
                }
            },
        )?;
        if let Some(e) = failure.into_inner() {
            return Err(e);
        }
        if let Some(e) = inline_failure.into_inner() {
            return Err(e);
        }
        let wanted: Vec<DefId> = (0..g.env.defs().len())
            .map(DefId)
            .filter(|id| reach.used[id.0] || reach.empty[id.0])
            .collect();
        // `reachable` skips a definition without a body, so make sure of the
        // rest.
        for &id in &wanted {
            self.try_info(id)?;
        }
        *self.used.borrow_mut() = reach.used;
        *self.empty.borrow_mut() = reach.empty;
        Ok(wanted)
    }

    /// Whether `id` applied to `args` is a call of its empty-row variant.
    pub(crate) fn empty_call(&self, id: DefId, args: &[&Term]) -> bool {
        self.empty.borrow()[id.0] && self.spec.empty_call(id, args).unwrap_or(false)
    }

    /// The [`DefInfo`] of `id`'s empty-row variant: its row parameters are
    /// erased.
    pub(crate) fn empty_info(&self, id: DefId) -> Fallible<&DefInfo> {
        if let Some(info) = self.empty_infos[id.0].get() {
            return Ok(info);
        }
        let info = self.info(id)?;
        let mask = self
            .spec
            .empty_mask(id, &info.mask)
            .unwrap_or_else(|_| info.mask.clone());
        let convention = if mask.iter().any(|erased| !erased) {
            Convention::Function
        } else {
            Convention::Thunk
        };
        Ok(self.empty_infos[id.0].get_or_init(|| DefInfo {
            result_erased: info.result_erased,
            uncurried: runtime_params(&mask) >= 2,
            mask,
            convention,
            delay: None,
        }))
    }

    /// The JS name of `id`, or of its empty-row variant: the name with
    /// `$e`, which no definition's name has, since [`encode`] uses `$`
    /// only for its escapes, none of which is `$e`.
    pub(crate) fn js_name(&self, id: DefId, variant: bool) -> String {
        if !variant && let Some(target) = self.aliases.borrow().get(&id) {
            return target.clone();
        }
        self.own_name(id, variant)
    }

    /// The name `id` (or its variant) is declared under, even if it's an
    /// alias ([`Gen::share`]).
    pub(crate) fn own_name(&self, id: DefId, variant: bool) -> String {
        let name = def_name(self.g.def(id).path());
        if variant { format!("{name}$e") } else { name }
    }

    /// Whether `id` applied to `args` is a call of the definition whose loop
    /// `call` is generating, with all its arguments: the same definition,
    /// and the variant if the loop is the variant's.
    pub(crate) fn is_self(&self, call: &SelfCall, id: DefId, args: &[&Term]) -> bool {
        id == call.id
            && args.len() == self.g.def(id).arity()
            && self.empty_call(id, args) == call.variant
    }

    /// Which kernel-native implementation applies to `id`, if any: the
    /// number natives assume the `bigint` representation, so they apply only
    /// with it ([`nat_data`]).
    pub(crate) fn kernel_native(&self, id: DefId) -> Option<native::Native> {
        self.nat.and(self.g.env.builtins().native(id))
    }

    /// The one run-time field of a record that generated code stores as
    /// that field's value, with no object around it (D866,
    /// [`stitchwort_core::globals::Data::unboxed_field`]). A `Float` is a
    /// `number` instead, when it has that representation. Only inside
    /// generated code: at the boundary such a record is still an object
    /// with its field, and the codecs unbox and rebox it.
    pub(crate) fn unboxed(&self, d: DataId) -> Option<usize> {
        if Some(d) == self.float || Some(d) == self.array {
            return None;
        }
        self.g.data(d).unboxed_field()
    }

    /// Whether `id` is replaced by native JS of any kind.
    pub(crate) fn is_native(&self, id: DefId) -> bool {
        self.kernel_native(id).is_some()
            || self.text_natives.contains_key(&id)
            || self.int_natives.contains_key(&id)
            || self.float_natives.contains_key(&id)
            || self.array_natives.contains_key(&id)
            || self.effect_native(id).is_some()
    }

    /// Which of the library functions the effect runtime replaces `id` is,
    /// if any.
    pub(crate) fn effect_native(&self, id: DefId) -> Option<effect::EffectNative> {
        self.effect.as_ref().and_then(|e| e.native(id))
    }

    /// What's decided about a definition, from its type: computed on first
    /// use, so a definition nothing extracted consults (a theorem, say) costs
    /// nothing.
    pub(crate) fn try_info(&self, id: DefId) -> Result<&DefInfo, Diagnostic> {
        let cell = &self.infos[id.0];
        if let Some(info) = cell.get() {
            return Ok(info);
        }
        let g = self.g;
        let def = g.def(id);
        // `Delay`'s constants have no body, so no arity: when they're run,
        // each takes all of its parameters ([`run::primitive_js`]).
        let shape = def_shape(g, id, self.run_delay)?;
        let delay = (shape.partial && !self.run_delay).then(|| shape.params.clone());
        let mask = shape.mask().to_vec();
        let result_erased = shape.result_erased;
        let convention = if result_erased {
            Convention::Erased
        } else if mask.iter().any(|e| !e) {
            Convention::Function
        } else {
            let case_tree = def.body().is_some_and(|b| {
                matches!(b.peel_lams(def.arity()), Term::Case(..) | Term::NumCase(..))
            });
            let in_group = def.group().as_ref().is_some_and(|m| m.len() > 1);
            if case_tree || in_group {
                Convention::Thunk
            } else {
                Convention::Value
            }
        };
        // A native takes all its arguments at once if its JS can be written
        // so (every native's can, but a check is cheaper than a wrong call).
        let runtime = runtime_params(&mask);
        let uncurried = convention == Convention::Function
            && delay.is_none()
            && runtime >= 2
            && (self.effect_native(id).is_some()
                || self
                    .native_rhs(id)
                    .is_none_or(|js| uncurry_arrows(&js, runtime).is_some()));
        Ok(cell.get_or_init(|| DefInfo {
            result_erased,
            mask,
            convention,
            uncurried,
            delay,
        }))
    }

    /// `try_info` for a definition the generator has already consulted:
    /// `generate_with` computes it for every definition it reaches.
    pub(crate) fn info(&self, id: DefId) -> Fallible<&DefInfo> {
        self.infos[id.0].get().ok_or_else(|| {
            let def = self.g.def(id);
            internal(format!("no information was computed for `{}`", def.path()))
                .with_label(def.span(), "while generating JavaScript for this")
        })
    }

    /// The declaration of `id` if the program uses it as it is, followed by
    /// its empty-row variant's if the program uses that.
    pub(crate) fn def(&self, id: DefId) -> Fallible<String> {
        let mut out = String::new();
        if self.used.borrow()[id.0] {
            let text = self.def_with(id, false)?;
            out.push_str(&self.share(id, text)?);
        }
        if self.empty.borrow()[id.0] {
            out.push_str(&self.def_with(id, true)?);
        }
        Ok(out)
    }

    /// `text`, the declaration `const f = …;` of `id`, unless `f` is, at run
    /// time, a definition generated before it, `g`: then `const f = g;`,
    /// and every later use of `f` names `g`. So a derived instance or
    /// comparison that only passes its arguments on to another's (an
    /// unboxed record's derived `Ord`, which compares its one field: SW-603)
    /// is that one, the same JS object, and code that takes a dictionary
    /// (`Map`, `List.unique`) sees one instance rather than one per type:
    /// its calls through the dictionary stay monomorphic for the engine.
    ///
    /// `f` is `g` when
    ///
    /// - `f` is a function that calls `g`, a function taking its arguments
    ///   the same way, with its own parameters in order and nothing else
    ///   (`(v0, v1) => g(v0, v1)`, through `const`s that rename them); or
    /// - `f` is a value whose right-hand side is `g`'s, or `g` itself.
    ///   Generated code is pure, and a module-level right-hand side refers
    ///   only to module-level names, so the same text is the same value.
    ///
    /// Only a definition generated earlier is a `g`, so `const f = g;`
    /// never reads `g` before it's defined.
    pub(crate) fn share(&self, id: DefId, text: String) -> Fallible<String> {
        let name = self.own_name(id, false);
        let info = self.info(id)?;
        let rhs = text
            .strip_prefix(&format!("const {name} = "))
            .and_then(|rest| rest.strip_suffix(";\n"));
        let target = match rhs {
            Some(rhs) => (|| -> Fallible<Option<String>> {
                Ok(match info.convention {
                    Convention::Function => {
                        let mut target = None;
                        if let Some(target_name) = forwards_to(rhs)
                            && let Some(&to) = self.emitted.borrow().get(target_name)
                        {
                            let to_info = self.info(to)?;
                            if to != id
                                && to_info.convention == Convention::Function
                                && to_info.uncurried == info.uncurried
                                && runtime_params(&to_info.mask) == runtime_params(&info.mask)
                            {
                                target = Some(target_name.to_string());
                            }
                        }
                        target
                    }
                    Convention::Value if !is_simple(rhs) => {
                        if let Some(&to) = self.emitted.borrow().get(rhs)
                            && self.info(to)?.convention == Convention::Value
                        {
                            return Ok(Some(rhs.to_string()));
                        }
                        let mut values = self.values.borrow_mut();
                        match values.get(rhs) {
                            Some(first) => Some(first.clone()),
                            None => {
                                values.insert(rhs.to_string(), name.clone());
                                None
                            }
                        }
                    }
                    _ => None,
                })
            })(),
            None => Ok(None),
        }?;
        self.emitted.borrow_mut().insert(name.clone(), id);
        Ok(match target {
            Some(target) => {
                let out = format!("const {name} = {target};\n");
                self.aliases.borrow_mut().insert(id, target);
                out
            }
            None => text,
        })
    }

    /// The declaration of `id`, or of its empty-row variant.
    pub(crate) fn def_with(&self, id: DefId, variant: bool) -> Fallible<String> {
        let def = self.g.def(id);
        let DefInfo {
            mask, convention, ..
        } = if variant {
            self.empty_info(id)?
        } else {
            self.info(id)?
        };
        let convention = *convention;
        if convention == Convention::Erased {
            return Ok(String::new());
        }
        if variant {
            let body = self
                .spec
                .empty_body(id)
                .ok()
                .flatten()
                .expect("a variant is used only if it can be made");
            return self.def_body(id, true, &body, mask, convention);
        }
        // The effect runtime's functions take all their arguments at once
        // already.
        if let Some(op) = self.effect_native(id) {
            return Ok(format!("const {} = {};\n", def_name(def.path()), op.js()));
        }
        if let Some(js) = self.native_rhs(id) {
            let info = self.info(id)?;
            let js = if info.uncurried {
                uncurry_arrows(&js, runtime_params(&info.mask))
                    .expect("`try_info` checked that it uncurries")
            } else {
                js
            };
            return Ok(format!("const {} = {js};\n", def_name(def.path())));
        }
        let Some(body) = def.run_body() else {
            unreachable!("`generate_with` refuses a definition without a body");
        };
        let body = body.clone();
        // Its calls of row eliminators with `Empty` inlined, if it has any.
        let simplified = self.spec.generic_body(id).ok().flatten();
        let tree = simplified
            .as_deref()
            .unwrap_or_else(|| body.peel_lams(def.arity()));
        self.def_body(id, false, tree, mask, convention)
    }

    /// The JS of `id` if it's native (other than the effect runtime's), as
    /// a function taking its runtime arguments one at a time.
    pub(crate) fn native_rhs(&self, id: DefId) -> Option<String> {
        if self.run_delay
            && let Some(prim) = self.g.env.builtins().primitive(id)
        {
            return Some(run::primitive_js(prim).into());
        }
        if let Some(op) = self.float_natives.get(&id) {
            return Some(float_native_js(
                *op,
                self.int.is_some(),
                self.text.is_some(),
            ));
        }
        if let Some(op) = self.text_natives.get(&id) {
            return Some(text_native_js(*op).into());
        }
        if let Some(op) = self.int_natives.get(&id) {
            return Some(int_native_js(*op).into());
        }
        if let Some(op) = self.array_natives.get(&id) {
            return Some(array_native_js(*op).into());
        }
        self.kernel_native(id).map(|op| native_js(op).into())
    }

    /// `const f = …;` for `id`, or its empty-row variant, with case tree
    /// (or body) `tree` under its parameters.
    pub(crate) fn def_body(
        &self,
        id: DefId,
        variant: bool,
        tree: &Term,
        mask: &[bool],
        convention: Convention,
    ) -> Fallible<String> {
        let name = self.own_name(id, variant);
        let mut env = mask.to_vec();
        let uncurried = if variant {
            self.empty_info(id)?
        } else {
            self.info(id)?
        }
        .uncurried;
        let runtime: Vec<String> = (0..mask.len())
            .filter(|level| !mask[*level])
            .map(var)
            .collect();
        let params = if runtime.is_empty() {
            String::new()
        } else if uncurried {
            format!("({}) => ", runtime.join(", "))
        } else {
            runtime.iter().map(|v| format!("({v}) => ")).collect()
        };
        let tree = tree.strip_loc();
        let rhs = if matches!(tree, Term::Case(..) | Term::NumCase(..)) {
            if !params.is_empty()
                && let Some(block) = self.self_tail_loop(id, variant, tree, &mut env)?
            {
                return Ok(format!("const {name} = {params}{block};\n"));
            }
            if !params.is_empty() {
                self.tailrec_not_looped(id, tree)?;
            }
            let block = self.tree(tree, &mut env, 1, None)?;
            match convention {
                Convention::Thunk => format!("() => {{\n{block}}}"),
                _ => format!("{{\n{block}}}"),
            }
        } else {
            // Not a case tree, but it may still reach a call to itself in
            // tail position: through a member of its group, inlined (a
            // lifted `match`), or through the `%rec` of a definition by
            // `decreasing`.
            if !params.is_empty()
                && self.may_loop(id, tree)
                && let Some(block) = self.self_tail_loop(id, variant, tree, &mut env)?
            {
                return Ok(format!("const {name} = {params}{block};\n"));
            }
            if !params.is_empty() {
                self.tailrec_not_looped(id, tree)?;
            }
            // After `=>`, leading `let`s are `const`s in a block.
            let rhs = if convention == Convention::Value {
                self.expr(tree, &mut env)?
            } else {
                self.function_body(tree, &mut env)?
            };
            match convention {
                Convention::Thunk => format!("() => {rhs}"),
                _ => rhs,
            }
        };
        Ok(format!("const {name} = {params}{rhs};\n"))
    }

    /// `@[tailrec]` promises a loop (docs/proposals/tailrec.md §3): a marked
    /// definition whose body didn't become one is a compiler bug, not a
    /// frame per call. Its recursion goes through the effect runtime's loop
    /// instead when its body binds effects, so those are exempt.
    pub(crate) fn tailrec_not_looped(&self, id: DefId, body: &Term) -> Fallible<()> {
        let def = self.g.def(id);
        if !def.tailrec() {
            return Ok(());
        }
        let binds_effects = body.subterms().any(|(t, _)| {
            matches!(t, Term::Def(d) if {
                let path = self.g.def(*d).path();
                path.starts_with("Std.Effect.bind")
            })
        });
        if binds_effects {
            return Ok(());
        }
        Err(internal(format!(
            "`{}` is marked @[tailrec], but the JavaScript backend could not make a loop of it, \
             so it would use a frame per call",
            def.path()
        ))
        .with_label(def.span(), "while generating JavaScript for this"))
    }

    /// If the definition `id`, with case tree `tree`, calls itself in tail
    /// position, its body as a loop, where each such call is another turn:
    ///
    /// ```js
    /// {
    ///   let s0 = v0, s1 = v1;
    ///   for (;;) {
    ///     const v0 = s0, v1 = s1;
    ///     … s0 = next0; s1 = next1; continue; …
    ///   }
    /// }
    /// ```
    ///
    /// Each turn has its own `const`s, so a closure made in one turn keeps
    /// that turn's values, and the parameters themselves are never assigned,
    /// so a partial application can be called again.
    pub(crate) fn self_tail_loop(
        &self,
        id: DefId,
        variant: bool,
        tree: &Term,
        env: &mut Vec<bool>,
    ) -> Fallible<Option<String>> {
        // The most it can do first: calls modulo constructors, through
        // inlined helpers. If that can't be compiled (a helper uses the
        // result some other way), less, and last, only direct tail calls.
        // Inlining without cons comes last: `List.decEq`'s step has no
        // constructor to build, only the call's result to return. Calls
        // modulo addition come after those modulo constructors: a result
        // that's a number is never a cell.
        for (cons, add, inline) in [
            (true, false, true),
            (true, false, false),
            (false, true, true),
            (false, true, false),
            (false, false, false),
            (false, false, true),
        ] {
            if add && self.nat_add.is_none() {
                continue;
            }
            let call = SelfCall::new(id, variant, cons, add, inline);
            self.holes.borrow_mut().clear();
            self.fn_holes.borrow_mut().clear();
            self.hole_misused.set(false);
            let block = self.tree(tree, env, 2, Some(&call))?;
            let ok = call.used.get()
                && !self.hole_misused.get()
                && (!cons || call.cons_used.get())
                && (!add || call.add_used.get());
            self.holes.borrow_mut().clear();
            self.fn_holes.borrow_mut().clear();
            self.hole_misused.set(false);
            if ok {
                return Ok(Some(Self::loop_block(env, &block, cons, add)));
            }
        }
        Ok(None)
    }

    /// Whether `body`, the body of definition `id` that isn't a case tree,
    /// mentions `id` or another member of its group: only then is
    /// [`Gen::self_tail_loop`] worth trying.
    pub(crate) fn may_loop(&self, id: DefId, body: &Term) -> bool {
        let group = self.g.def(id).group().as_deref().unwrap_or(&[]);
        body.subterms().any(|(t, _)| match t {
            Term::Def(d) => *d == id || group.contains(d),
            _ => false,
        })
    }

    /// Whether `member`, called in tail position in the loop of `call`'s
    /// definition, is inlined there, so that its own tail calls to that
    /// definition are turns of the loop. It's another member of the group,
    /// not one already being inlined, and either
    ///
    /// - a `match` lifted out of the definition (`f.%match1`, or one nested
    ///   in it), which calls a member: it's inlined wherever it's used,
    ///   since there are only as many as the source has `match`es; or
    /// - a member that calls the definition itself (`isOdd`, in `isEven`'s
    ///   loop). One that only calls other members isn't, so that a big group
    ///   doesn't inline chains of members into each other: a cycle of three
    ///   or more such members still uses a stack frame per call.
    ///
    /// A definition isn't inlined into a `match` lifted out of it:
    /// `f.%match1` calls `f`, which loops, rather than holding a copy of it.
    pub(crate) fn inlines_member(&self, member: DefId, call: &SelfCall) -> bool {
        let def = self.g.def(call.id);
        let Some(group) = def.group().as_deref() else {
            return false;
        };
        // A member's body is the generic one, which a variant's loop
        // doesn't reach: it calls the member's variant instead.
        if call.variant {
            return false;
        }
        if member == call.id || !group.contains(&member) || call.inlined.borrow().contains(&member)
        {
            return false;
        }
        let member_def = self.g.def(member);
        let path = def.path().to_string();
        let member_path = member_def.path().to_string();
        if path.starts_with(&format!("{member_path}.%")) {
            return false;
        }
        let lifted = member_path.starts_with(&format!("{path}.%"));
        member_def.run_body().is_some_and(|body| {
            body.subterms().any(|(t, _)| match t {
                Term::Def(d) => *d == call.id || (lifted && group.contains(d)),
                _ => false,
            })
        })
    }

    /// The loop of [`Gen::self_tail_loop`], around the case tree's `block`.
    /// With `cons`, the result is built by a chain of cells (a constructor's
    /// object) that the loop links as it makes them: `h$` is the first, `l$`
    /// the last, and `k$` the name of its field that the rest goes in. With
    /// `add`, `a$` is what the result is to be added to.
    pub(crate) fn loop_block(env: &[bool], block: &str, cons: bool, add: bool) -> String {
        let slots: Vec<usize> = (0..env.len()).filter(|level| !env[*level]).collect();
        let copy = |from: fn(usize) -> String, to: fn(usize) -> String| {
            slots
                .iter()
                .map(|level| format!("{} = {}", to(*level), from(*level)))
                .collect::<Vec<_>>()
                .join(", ")
        };
        let chain = if cons {
            "  let h$ = null, l$ = null, k$ = null;\n"
        } else if add {
            "  let a$ = 0n;\n"
        } else {
            ""
        };
        format!(
            "{{\n  let {};\n{chain}  for (;;) {{\n    const {};\n{block}  }}\n}}",
            copy(var, slot),
            copy(slot, var)
        )
    }

    /// Statements for a case tree, ending in `return` (or, for a call to
    /// `self_call` in tail position, `continue`). `env` says, for each
    /// variable level, whether it's erased.
    pub(crate) fn tree(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        depth: usize,
        self_call: Option<&SelfCall>,
    ) -> Fallible<String> {
        self.g.machine.budget.nesting(PASS)?;
        let pad = "  ".repeat(depth);
        if let Term::NumCase(ix, arms, default) = term.strip_loc() {
            // Each arm ends in `return` (or `continue`), so nothing falls
            // through, and after the `switch` comes the default.
            let scrutinee = self.scrutinee(env, *ix);
            let mut out = format!("{pad}switch ({scrutinee}) {{\n");
            for arm in arms.iter() {
                let _ = writeln!(out, "{pad}  case {}n: {{", arm.value);
                out.push_str(&self.tree(&arm.body, env, depth + 2, self_call)?);
                let _ = writeln!(out, "{pad}  }}");
            }
            let _ = writeln!(out, "{pad}}}");
            out.push_str(&self.tree(default, env, depth, self_call)?);
            return Ok(out);
        }
        if let Term::Let(_, _, value, body, erased, _) = term.strip_loc() {
            let mut out = self.let_statement(value, *erased, env, &pad)?;
            out.push_str(&self.tree(body, env, depth, self_call)?);
            env.pop();
            return Ok(out);
        }
        let Term::Case(ix, d, branches) = term.strip_loc() else {
            return match self_call {
                Some(call) => self.tail(term, env, depth, call),
                None => Ok(format!("{pad}return {};\n", self.expr(term, env)?)),
            };
        };
        // A match on the result of the call to itself (inside an inlined
        // helper) that gives the same constructor back, fields erased, is
        // that result: the call is in tail position after all.
        if let Some(call) = self_call
            && self.hole_at(env.len() - 1 - *ix).is_some()
            && self.is_identity_match(*d, branches)
        {
            return self.tail(&Term::Var(*ix), env, depth, call);
        }
        let data = self.g.data(*d);
        let scrutinee = self.scrutinee(env, *ix);
        let mut out = String::new();
        let predecessor = var(env.len());
        // A record stored as its one run-time field (D866): that field is the
        // value matched.
        let unboxed = self.unboxed(*d).is_some();
        let mut branch = |out: &mut String, c: usize, b: &Branch, depth: usize| -> Fallible<()> {
            let pad = "  ".repeat(depth);
            let level = env.len();
            for (f, ((_, _), erased)) in data.ctors()[c]
                .fields
                .iter()
                .zip(&data.ctors()[c].field_erased)
                .enumerate()
            {
                if !erased && Some(*d) == self.float {
                    // A `Float` is a `number`: its one runtime field is
                    // its bits.
                    let _ = writeln!(
                        out,
                        "{pad}const {} = toCanonicalBits({scrutinee});",
                        var(level + f)
                    );
                } else if !erased && unboxed {
                    let _ = writeln!(out, "{pad}const {} = {scrutinee};", var(level + f));
                } else if !erased && Some(*d) != self.nat && Some(*d) != self.int {
                    let _ = writeln!(
                        out,
                        "{pad}const {} = {scrutinee}{};",
                        var(level + f),
                        member(&field_key_at(self.g, *d, c, f))
                    );
                }
                env.push(*erased);
            }
            match &b.body {
                Some(body) => out.push_str(&self.tree(body, env, depth, self_call)?),
                // An impossible branch (docs/proposals/indexed-families.md
                // §6.8): never reached by a well-typed value.
                None => {
                    let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
                }
            }
            env.truncate(level);
            Ok(())
        };
        if data.sort() == Sort::Prop {
            // The proof doesn't exist at runtime. Matching on it into data is
            // only allowed for at most one constructor with only proof fields.
            match branches.first() {
                Some(b) => branch(&mut out, 0, b, depth)?,
                None => {
                    let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
                }
            }
        } else if Some(*d) == self.nat {
            let _ = writeln!(out, "{pad}if ({scrutinee} === 0n) {{");
            branch(&mut out, 0, &branches[0], depth + 1)?;
            let _ = writeln!(out, "{pad}}} else {{");
            let _ = writeln!(out, "{pad}  const {predecessor} = {scrutinee} - 1n;");
            branch(&mut out, 1, &branches[1], depth + 1)?;
            let _ = writeln!(out, "{pad}}}");
        } else if Some(*d) == self.int {
            // A `bigint`: `OfNat n` is `n` itself, and `NegSucc n` is
            // `-n - 1n`, so the sign tells them apart, and `-x - 1n` gives
            // `NegSucc`'s field back.
            let field = predecessor;
            let _ = writeln!(out, "{pad}if ({scrutinee} >= 0n) {{");
            let _ = writeln!(out, "{pad}  const {field} = {scrutinee};");
            branch(&mut out, 0, &branches[0], depth + 1)?;
            let _ = writeln!(out, "{pad}}} else {{");
            let _ = writeln!(out, "{pad}  const {field} = -{scrutinee} - 1n;");
            branch(&mut out, 1, &branches[1], depth + 1)?;
            let _ = writeln!(out, "{pad}}}");
        } else if Some(*d) == self.text {
            // A `Text` is a string. Matching `MkText cs` makes the list of
            // its characters, in a loop, but only if `cs` is used.
            let level = env.len();
            env.push(false);
            let body = match &branches[0].body {
                Some(body) => self.tree(body, env, depth, self_call)?,
                None => format!("{pad}throw new Error(\"unreachable\");\n"),
            };
            env.truncate(level);
            if mentions(&body, &var(level)) {
                let _ = writeln!(out, "{pad}const {} = charsOfText({scrutinee});", var(level));
            }
            out.push_str(&body);
        } else if Some(*d) == self.array {
            // A version array. Matching `{ toList = xs }` makes the list of
            // its elements, but only if `xs` is used.
            let level = env.len();
            env.push(false);
            let body = match &branches[0].body {
                Some(body) => self.tree(body, env, depth, self_call)?,
                None => format!("{pad}throw new Error(\"unreachable\");\n"),
            };
            env.truncate(level);
            if mentions(&body, &var(level)) {
                let _ = writeln!(out, "{pad}const {} = listOfArray({scrutinee});", var(level));
            }
            out.push_str(&body);
        } else if data.record() {
            // A record has one constructor and no tag.
            branch(&mut out, 0, &branches[0], depth)?;
        } else {
            let _ = writeln!(out, "{pad}switch ({scrutinee}.tag) {{");
            for (c, b) in branches.iter().enumerate() {
                let _ = writeln!(out, "{pad}  case \"{}\": {{", data.ctors()[c].name);
                branch(&mut out, c, b, depth + 2)?;
                let _ = writeln!(out, "{pad}  }}");
            }
            let _ = writeln!(out, "{pad}}}");
            let _ = writeln!(out, "{pad}throw new Error(\"unreachable\");");
        }
        Ok(out)
    }

    /// What `id` does at run time, if its run-time body only applies one
    /// of its parameters to others (or gives one back), seen through what
    /// an unboxed record is at run time (its one runtime field, D866) and
    /// through calls of other such definitions: the parameters' positions,
    /// the function's and its arguments'. `Decidable.holds` and
    /// `Decidable.map` give their decision back (a decision is stored as
    /// its test), `DecEq.%decide` its dictionary, and `DecEq.decide d x y`
    /// is `d x y`. A full call of one is that application
    /// ([`Gen::passed_through`]).
    pub(crate) fn forwarder(&self, id: DefId) -> Option<Forward> {
        if let Some(known) = self.forwarders.borrow().get(&id) {
            return known.clone();
        }
        // Not one while it's being worked out, so definitions that forward
        // to each other end.
        self.forwarders.borrow_mut().insert(id, None);
        let found = self.find_forwarder(id);
        self.forwarders.borrow_mut().insert(id, found.clone());
        found
    }

    pub(crate) fn find_forwarder(&self, id: DefId) -> Option<Forward> {
        if self.is_native(id) {
            return None;
        }
        let def = self.g.def(id);
        let arity = def.arity();
        let mut body = def.run_body()?.strip_loc().clone();
        for _ in 0..arity {
            let Term::Lam(_, _, inner, _) = &body else {
                return None;
            };
            body = inner.strip_loc().clone();
        }
        let mut steps = 0;
        while let Some(next) = self.passed_through(&body) {
            body = next.strip_loc().clone();
            steps += 1;
            if steps > 8 {
                return None;
            }
        }
        let info = self.try_info(id).ok()?;
        if info.convention != Convention::Function {
            return None;
        }
        let position = |t: &Term| match t.strip_loc() {
            Term::Var(ix) => arity.checked_sub(ix + 1).filter(|k| !info.mask[*k]),
            _ => None,
        };
        let (head, args) = body.spine();
        let f = position(head)?;
        let args = args.into_iter().map(position).collect::<Option<Vec<_>>>()?;
        Some((f, args))
    }

    /// `term` as the same value at run time one step on, if that's
    /// simpler: an unboxed record's constructor is its runtime field, a
    /// projection of that field the record, and a full call of a
    /// [`Gen::forwarder`] definition the application it makes (applied
    /// to any arguments after). So a loop sees a call to itself through
    /// `Decidable.map` and `Decidable.and`, as `List.decEq` makes one.
    pub(crate) fn passed_through(&self, term: &Term) -> Option<Term> {
        match term.strip_loc() {
            Term::Ctor(d, 0, fields) => Some((*fields[self.unboxed(*d)?]).clone()),
            Term::Proj(d, i, x) if self.unboxed(*d) == Some(*i) => Some((**x).clone()),
            // A match on an unboxed record giving its runtime field (a
            // projection function's body) is the record.
            Term::Case(ix, d, branches) if branches.len() == 1 => {
                let k = self.unboxed(*d)?;
                let branch = &branches[0];
                let n = branch.names.len();
                match branch.body.as_ref()?.strip_loc() {
                    Term::Var(j) if j + 1 + k == n => Some(Term::Var(*ix)),
                    Term::Var(j) if *j >= n => Some(Term::Var(j - n)),
                    _ => None,
                }
            }
            _ => {
                let (head, args) = term.spine();
                let Term::Def(id) = head else {
                    return None;
                };
                let arity = self.g.def(*id).arity();
                if args.len() < arity || self.empty_call(*id, &args) {
                    return None;
                }
                let (f, passed) = self.forwarder(*id)?;
                let mut out = args[f].clone();
                for k in passed {
                    out = Term::app(out, args[k].clone());
                }
                for arg in &args[arity..] {
                    out = Term::app(out, (*arg).clone());
                }
                Some(out)
            }
        }
    }

    /// The function a constant gives at run time, if its run-time body is
    /// one: a definition, or a lambda that passes its parameters on to one,
    /// seen through unboxed records. So a call through an instance with one
    /// method, `Text.instDecEq`, is a call of that method's definition,
    /// `Text.decEq`.
    pub(crate) fn known_function(&self, id: DefId) -> Option<DefId> {
        let def = self.g.def(id);
        if def.arity() != 0 || self.is_native(id) {
            return None;
        }
        let mut body = def.run_body()?.strip_loc().clone();
        for _ in 0..8 {
            let Some(next) = self.passed_through(&body) else {
                break;
            };
            body = next.strip_loc().clone();
        }
        let mut lams = 0;
        let mut inner = &body;
        while let Term::Lam(_, _, b, _) = inner.strip_loc() {
            lams += 1;
            inner = b;
        }
        let (head, args) = inner.spine();
        let Term::Def(f) = head.strip_loc() else {
            return None;
        };
        let forwards = args.len() == lams
            && args
                .iter()
                .enumerate()
                .all(|(i, a)| matches!(a.strip_loc(), Term::Var(ix) if *ix == lams - 1 - i));
        (forwards && *f != id).then_some(*f)
    }

    /// Whether a match on a value of data type `d` gives back, in each
    /// branch, the constructor it matched, whose fields are all erased: so
    /// the match is the value itself.
    pub(crate) fn is_identity_match(&self, d: DataId, branches: &[Branch]) -> bool {
        let data = self.g.data(d);
        if data.sort() == Sort::Prop
            || data.record()
            || Some(d) == self.float
            || Some(d) == self.array
            || Some(d) == self.text
            || Some(d) == self.nat
            || Some(d) == self.int
        {
            return false;
        }
        branches.iter().enumerate().all(|(c, b)| {
            data.ctors()[c].field_erased.iter().all(|erased| *erased)
                && matches!(
                    b.body.as_ref().map(|body| body.strip_loc()),
                    Some(Term::Ctor(d2, c2, _)) if *d2 == d && *c2 == c
                )
        })
    }

    /// A `let` in statement position: `const v = value;`, or nothing for
    /// one the kernel marked skipped (a proof, a type, or unused;
    /// docs/proposals/let.md §6.1 rule 5). Adds its variable to `env`,
    /// which the caller removes after the body.
    pub(crate) fn let_statement(
        &self,
        value: &Term,
        erased: bool,
        env: &mut Vec<bool>,
        pad: &str,
    ) -> Fallible<String> {
        if erased {
            env.push(true);
            return Ok(String::new());
        }
        let line = format!(
            "{pad}const {} = {};\n",
            var(env.len()),
            self.expr(value, env)?
        );
        env.push(false);
        Ok(line)
    }

    /// A leaf of the case tree of a definition that's being made a loop
    /// ([`Gen::self_tail_loop`]). A call to itself with all its arguments is
    /// another turn. `if` is written out as a JS `if`, so that calls in its
    /// branches are in tail position too.
    pub(crate) fn tail(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        depth: usize,
        call: &SelfCall,
    ) -> Fallible<String> {
        self.g.machine.budget.nesting(PASS)?;
        let pad = "  ".repeat(depth);
        if let Term::Let(_, _, value, body, erased, _) = term.strip_loc() {
            let mut out = self.let_statement(value, *erased, env, &pad)?;
            out.push_str(&self.tail(body, env, depth, call)?);
            env.pop();
            return Ok(out);
        }
        // A function that stands for a call to itself, applied: the call,
        // with the arguments bound to its parameters.
        if let Some(reduced) = self.apply_fn_hole(term, env.len())? {
            return self.tail(&reduced, env, depth, call);
        }
        if let Some(same) = self.passed_through(term) {
            return self.tail(&same, env, depth, call);
        }
        // A variable that stands for a call to itself, in a helper that's
        // been inlined: the next turn.
        if let Term::Var(ix) = term.strip_loc()
            && let Some(passed) = self.hole_at(env.len() - 1 - ix)
        {
            call.used.set(true);
            return Ok(Self::next_turn(&pad, &passed));
        }
        // A constructor with the call in a field: the call is the next turn,
        // and its result will be put in that field of this cell.
        if call.cons
            && let Term::Ctor(..) = term.strip_loc()
            && let Some(path) = self.hole_path(term, env, call)
        {
            let mut out = String::new();
            let (cell, last_cell, key, passed) =
                self.cons_cells(term, env, &pad, call, &path, &mut out)?;
            call.cons_used.set(true);
            call.used.set(true);
            let _ = writeln!(
                out,
                "{pad}if (l$ === null) {{ h$ = {cell}; }} else {{ l$[k$] = {cell}; }}"
            );
            let _ = writeln!(
                out,
                "{pad}l$ = {last_cell}; k$ = {};",
                js_string_literal(&key)
            );
            out.push_str(&Self::next_turn(&pad, &passed));
            return Ok(out);
        }
        if call.add
            && let Some(out) = self.tail_add(term, env, &pad, call)?
        {
            return Ok(out);
        }
        if call.cons
            && let Some(out) = self.tail_append(term, env, &pad, call)?
        {
            return Ok(out);
        }
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return self.leaf_return(term, env, &pad, call);
        };
        if self.is_self(call, *id, &args) {
            call.used.set(true);
            let mut passed = Vec::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    passed.push((level, self.expr(arg, env)?));
                }
            }
            return Ok(Self::next_turn(&pad, &passed));
        }
        if let Some((cond, then, otherwise, tag)) = self.conditional(*id, &args) {
            let cond = self.expr(cond, env)?;
            // The branches' parameter is a proof (of `Unit`, of `p` or of
            // `Not p`), so it's erased.
            let mut branch = |body: &Term| -> Fallible<String> {
                env.push(true);
                let out = self.tail(body, env, depth + 1, call);
                env.pop();
                out
            };
            let then = branch(then)?;
            let otherwise = branch(otherwise)?;
            return Ok(format!(
                "{pad}if ({cond}.tag === {}) {{\n{then}{pad}}} else {{\n{otherwise}{pad}}}\n",
                js_string_literal(&tag)
            ));
        }
        if call.inline
            && call.inlining.get() < 3
            && let Some(out) = self.inline_helper(*id, &args, env, depth, call)?
        {
            return Ok(out);
        }
        self.leaf_return(term, env, &pad, call)
    }

    /// If `term` is a call to the definition itself (or a variable that
    /// stands for one) under `Succ`s and `Nat.add`s, with the other operands
    /// not mentioning it: the next turn, after adding those operands to
    /// `a$` (tail recursion modulo addition, [`SelfCall::add`]). Addition
    /// is associative and commutative, so `x + f(..)` is `f(..)` with `x`
    /// added to the sum, wherever the call is among the operands.
    pub(crate) fn tail_add(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        // The other operands, and the call.
        let mut addends: Vec<&Term> = Vec::new();
        let mut ones = 0u64;
        let mut inner = term.strip_loc();
        loop {
            if let Term::Ctor(d, 1, succ) = inner
                && Some(*d) == self.nat
            {
                ones += 1;
                inner = succ[0].strip_loc();
                continue;
            }
            let (head, args) = inner.spine();
            if let Term::Def(id) = head
                && Some(*id) == self.nat_add
                && let [left, right] = args.as_slice()
            {
                let in_left = self.self_call_under_add(left, env, call);
                let in_right = self.self_call_under_add(right, env, call);
                if in_left == in_right {
                    return Ok(None);
                }
                let (operand, rest) = if in_left {
                    (right, left)
                } else {
                    (left, right)
                };
                addends.push(operand);
                inner = rest.strip_loc();
                continue;
            }
            break;
        }
        if addends.is_empty() && ones == 0 {
            return Ok(None);
        }
        let Some(passed) = self.hole_passed(inner, env, call)? else {
            return Ok(None);
        };
        let mut out = String::new();
        for addend in addends {
            let _ = writeln!(out, "{pad}a$ += {};", self.expr(addend, env)?);
        }
        if ones > 0 {
            let _ = writeln!(out, "{pad}a$ += {ones}n;");
        }
        call.add_used.set(true);
        call.used.set(true);
        out.push_str(&Self::next_turn(pad, &passed));
        Ok(Some(out))
    }

    /// Whether `term` is a call to the definition itself, or a variable
    /// that stands for one, under `Succ`s and `Nat.add`s ([`Gen::tail_add`]):
    /// exactly one of an addition's operands must hold it, so the answer is
    /// whether an odd number of the leaves are such calls. A work list, not
    /// recursion: `a + (b + (c + …))` can nest deeper than the stack
    /// (docs/core.md). (Nothing is generated.)
    pub(crate) fn self_call_under_add(&self, term: &Term, env: &[bool], call: &SelfCall) -> bool {
        let mut pending = vec![term];
        let mut odd = false;
        while let Some(term) = pending.pop() {
            let term = term.strip_loc();
            if let Term::Ctor(d, 1, succ) = term
                && Some(*d) == self.nat
            {
                pending.push(&succ[0]);
                continue;
            }
            if let Term::Var(ix) = term {
                odd ^= self.hole_at(env.len() - 1 - ix).is_some();
                continue;
            }
            let (head, args) = term.spine();
            match head {
                Term::Def(id) if self.is_self(call, *id, &args) => odd = !odd,
                Term::Def(id) if Some(*id) == self.nat_add && args.len() == 2 => {
                    pending.extend([args[0], args[1]]);
                }
                _ => {}
            }
        }
        odd
    }

    /// If `term` is `List.append xs rest`, where `rest` is a call to the
    /// definition itself (or a variable that stands for one): copies of
    /// `xs`'s cells linked onto the chain, then the next turn, whose result
    /// goes after them (tail recursion modulo append: `List.concat`'s
    /// `List.append xs (List.concat xss)`). `List.append` copies its first
    /// argument and shares its second, as this does.
    pub(crate) fn tail_append(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        let (head, args) = term.spine();
        let Term::Def(id) = head else {
            return Ok(None);
        };
        if Some(*id) != self.list_append || args.len() != self.g.def(*id).arity() || args.len() < 2
        {
            return Ok(None);
        }
        let (front, rest) = (args[args.len() - 2], args[args.len() - 1]);
        let Some(list) = self.g.env.registry().data(Builtin::List) else {
            return Ok(None);
        };
        let Some(cons) = self
            .g
            .data(list)
            .ctors()
            .iter()
            .position(|c| &*c.name == "Cons")
        else {
            return Ok(None);
        };
        if self.hole_passed_shape(rest, env, call).is_none() {
            return Ok(None);
        }
        // `xs` is computed first, as the call's first argument was.
        let front = self.expr(front, env)?;
        let passed = self
            .hole_passed(rest, env, call)?
            .expect("`hole_passed_shape` found a call");
        let tag = js_string_literal(&self.g.data(list).ctors()[cons].name);
        let head_key = field_key_at(self.g, list, cons, 0);
        let tail_key = field_key_at(self.g, list, cons, 1);
        let n = call.fresh();
        let mut out = String::new();
        let _ = writeln!(
            out,
            "{pad}for (let p{n}$ = {front}; p{n}$.tag === {tag}; p{n}$ = p{n}${}) {{",
            member(&tail_key)
        );
        let _ = writeln!(
            out,
            "{pad}  const c{n}$ = {{ tag: {tag}, {}: p{n}${}, {}: null }};",
            ts_key(&head_key),
            member(&head_key),
            ts_key(&tail_key)
        );
        let _ = writeln!(
            out,
            "{pad}  if (l$ === null) {{ h$ = c{n}$; }} else {{ l$[k$] = c{n}$; }}"
        );
        let _ = writeln!(
            out,
            "{pad}  l$ = c{n}$; k$ = {};",
            js_string_literal(&tail_key)
        );
        let _ = writeln!(out, "{pad}}}");
        call.cons_used.set(true);
        call.used.set(true);
        out.push_str(&Self::next_turn(pad, &passed));
        Ok(Some(out))
    }

    /// Whether `term` is a call to the definition itself, or a variable
    /// that stands for one. (Nothing is generated.)
    fn hole_passed_shape(&self, term: &Term, env: &[bool], call: &SelfCall) -> Option<()> {
        if let Term::Var(ix) = term.strip_loc() {
            return self.hole_at(env.len() - 1 - ix).map(|_| ());
        }
        let (head, args) = term.spine();
        matches!(head, Term::Def(id) if self.is_self(call, *id, &args)).then_some(())
    }

    /// `term`, a leaf of a loop that isn't another turn, is its result. If
    /// the loop is building a chain of cells, it's the rest of the chain.
    pub(crate) fn leaf_return(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
    ) -> Fallible<String> {
        let value = self.expr(term, env)?;
        Ok(if call.cons {
            format!(
                "{pad}{{ const r$ = {value}; if (l$ === null) return r$; l$[k$] = r$; return h$; }}\n"
            )
        } else if call.add && value == "0n" {
            format!("{pad}return a$;\n")
        } else if call.add {
            format!("{pad}return a$ + {value};\n")
        } else {
            format!("{pad}return {value};\n")
        })
    }

    /// The next turn of a loop, passing `passed` (parameter level and JS
    /// value).
    pub(crate) fn next_turn(pad: &str, passed: &[(usize, String)]) -> String {
        let mut out = String::new();
        for (level, value) in passed {
            let _ = writeln!(out, "{pad}{} = {value};", slot(*level));
        }
        let _ = writeln!(out, "{pad}continue;");
        out
    }

    /// What the next turn would be passed, if variable `level` stands for a
    /// call to the definition itself.
    pub(crate) fn hole_at(&self, level: usize) -> Option<Vec<(usize, String)>> {
        self.holes
            .borrow()
            .iter()
            .rev()
            .find(|(l, _)| *l == level)
            .map(|(_, passed)| passed.clone())
    }

    /// The variable for `ix`, as a case's scrutinee. A variable that stands
    /// for a call to itself has no value, so it can't be matched on.
    pub(crate) fn scrutinee(&self, env: &[bool], ix: usize) -> String {
        let level = env.len() - 1 - ix;
        if self.hole_at(level).is_some() || self.is_fn_hole(level) {
            self.hole_misused.set(true);
        }
        var(level)
    }

    /// If `term` is a call to the definition itself, or a variable that
    /// stands for one, what the next turn would be passed.
    pub(crate) fn hole_passed(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        call: &SelfCall,
    ) -> Fallible<Option<Vec<(usize, String)>>> {
        if let Term::Var(ix) = term.strip_loc() {
            return Ok(self.hole_at(env.len() - 1 - ix));
        }
        let (head, args) = term.spine();
        if let Term::Def(id) = head
            && self.is_self(call, *id, &args)
        {
            let mut passed = Vec::new();
            for (level, arg) in args.iter().enumerate() {
                if !env[level] {
                    passed.push((level, self.expr(arg, env)?));
                }
            }
            return Ok(Some(passed));
        }
        Ok(None)
    }

    /// Whether `term` has a call to the definition itself (or a variable
    /// that stands for one) as a field, or in a constructor in a field:
    /// the fields leading to it, outermost first, if only one has it.
    /// (Nothing is generated.)
    fn hole_path(&self, term: &Term, env: &[bool], call: &SelfCall) -> Option<Vec<usize>> {
        let mut path = Vec::new();
        self.hole_path_into(term, env, call, &mut path)
            .then_some(path)
    }

    /// [`Gen::hole_path`], appending the fields to `path`: true if there is
    /// exactly one, and none of them is erased.
    pub(crate) fn hole_path_into(
        &self,
        term: &Term,
        env: &[bool],
        call: &SelfCall,
        path: &mut Vec<usize>,
    ) -> bool {
        let Term::Ctor(d, c, args) = term.strip_loc() else {
            return false;
        };
        let data = self.g.data(*d);
        // A record stored as its field (D866) is no cell either.
        if data.sort() == Sort::Prop
            || Some(*d) == self.text
            || Some(*d) == self.nat
            || Some(*d) == self.int
            || Some(*d) == self.float
            || Some(*d) == self.array
            || self.unboxed(*d).is_some()
        {
            return false;
        }
        let before = path.len();
        let mut found = false;
        for (i, arg) in args.iter().enumerate() {
            path.push(i);
            let is_hole = match arg.strip_loc() {
                Term::Var(ix) => self.hole_at(env.len() - 1 - ix).is_some(),
                Term::Ctor(..) => self.hole_path_into(arg, env, call, path),
                other => {
                    let (head, args) = other.spine();
                    matches!(head, Term::Def(id) if self.is_self(call, *id, &args))
                }
            };
            if !is_hole {
                path.pop();
            } else if found || data.ctors()[*c].field_erased[i] {
                // Two holes, or the field is erased: there's no cell to put
                // it in.
                path.truncate(before);
                return false;
            } else {
                found = true;
            }
        }
        found
    }

    /// Statements that make the cells of `term` (a constructor with a call
    /// to itself in a field, [`Gen::hole_path`]), and what to do next:
    /// the outermost cell, the innermost, the field of the innermost that
    /// takes the rest, and what the next turn is passed. The cells' other
    /// fields are computed now, as the whole constructor would have been.
    pub(crate) fn cons_cells(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        pad: &str,
        call: &SelfCall,
        path: &[usize],
        out: &mut String,
    ) -> Fallible<Cells> {
        let Term::Ctor(d, c, args) = term.strip_loc() else {
            unreachable!("`hole_path` found a constructor");
        };
        let hole = *path.first().expect("`hole_path` found a hole");
        let data = self.g.data(*d);
        let ctor = &data.ctors()[*c];
        let mut fields = Vec::new();
        if !data.record() {
            fields.push(format!("tag: \"{}\"", ctor.name));
        }
        let mut inner = None;
        for (f, (erased, arg)) in ctor.field_erased.iter().zip(args.iter()).enumerate() {
            if *erased {
                continue;
            }
            let key = field_key_at(self.g, *d, *c, f);
            let value = if f != hole {
                self.expr(arg, env)?
            } else if let Term::Ctor(..) = arg.strip_loc() {
                let (cell, last, last_key, passed) =
                    self.cons_cells(arg, env, pad, call, &path[1..], out)?;
                inner = Some((last, last_key, passed));
                cell
            } else {
                let passed = self
                    .hole_passed(arg, env, call)?
                    .expect("`hole_path` found a call");
                inner = Some((String::new(), key.clone(), passed));
                "null".to_string()
            };
            fields.push(format!("{}: {value}", ts_key(&key)));
        }
        let cell = format!("c{}$", call.fresh());
        let _ = writeln!(out, "{pad}const {cell} = {{ {} }};", fields.join(", "));
        let (last, key, passed) = inner.expect("the hole's field is not erased");
        // A direct call: this cell is the last, and the field is its own.
        let last = if last.is_empty() { cell.clone() } else { last };
        Ok((cell, last, key, passed))
    }

    /// A call to `id`, with `args`, in tail position, where some of the
    /// arguments are calls to the definition itself: if `id` is a helper
    /// that only matches on its other arguments, it's inlined, so that
    /// the calls are in tail position in its case tree: `List.filter`'s
    /// `List.filterStep x (List.filter p xs) (p x)`, where the step has
    /// the rest as the tail of a `Cons`, or as itself. The calls' results
    /// are variables that can only be used in tail position or in a
    /// constructor there ([`Gen::hole_misused`]).
    ///
    /// The same for an argument that's a function whose body is such a
    /// call, which the helper may only apply, in those places: a
    /// definition by `decreasing` runs `f.%step x (y c p => f y c) c`
    /// ([`Gen::fn_holes`]). And for a call to another member of the
    /// definition's group ([`Gen::inlines_member`]), whose own calls to the
    /// definition are then in tail position here.
    pub(crate) fn inline_helper(
        &self,
        id: DefId,
        args: &[&Term],
        env: &mut Vec<bool>,
        depth: usize,
        call: &SelfCall,
    ) -> Fallible<Option<String>> {
        let def = self.g.def(id);
        if id == call.id || def.arity() != args.len() || self.is_native(id) {
            return Ok(None);
        }
        let Some(info) = self.infos[id.0].get() else {
            return Ok(None);
        };
        let variant = self.empty_call(id, args);
        let info = if variant { self.empty_info(id)? } else { info };
        if info.convention != Convention::Function || info.delay.is_some() {
            return Ok(None);
        }
        let tree = if variant {
            match self.spec.empty_body(id) {
                Ok(Some(body)) => body,
                _ => return Ok(None),
            }
        } else {
            match (self.spec.generic_body(id).ok().flatten(), def.run_body()) {
                (Some(simplified), _) => simplified,
                (None, Some(body)) => Rc::new(body.peel_lams(def.arity()).clone()),
                (None, None) => return Ok(None),
            }
        };
        // The arguments, in this call's environment. A call to itself isn't
        // made: it's the next turn, if the helper puts it in tail position.
        enum Bound {
            Erased,
            Value(String),
            Hole(Passed),
            /// The parameters, the body, and the environment's size there.
            FnHole(Vec<stitchwort_core::Name>, Term, usize),
        }
        let member = self.inlines_member(id, call);
        let mut bound = Vec::new();
        let mut any_hole = false;
        for (i, arg) in args.iter().enumerate() {
            if info.mask[i] {
                bound.push(Bound::Erased);
            } else if let Some(passed) = self.hole_passed(arg, env, call)? {
                any_hole = true;
                bound.push(Bound::Hole(passed));
            } else if let Some((params, body)) = self.fn_hole_arg(arg, call) {
                any_hole = true;
                bound.push(Bound::FnHole(params, body, env.len()));
            } else if let Term::Var(ix) = arg.strip_loc()
                && let Some(hole) = self
                    .fn_holes
                    .borrow()
                    .iter()
                    .rfind(|h| h.level == env.len() - 1 - ix)
            {
                // Passed on (to a `match` lifted out of `f.%step`): it
                // stands for the same function there.
                any_hole = true;
                bound.push(Bound::FnHole(
                    hole.params.clone(),
                    hole.body.clone(),
                    hole.site,
                ));
            } else {
                bound.push(Bound::Value(self.expr(arg, env)?));
            }
        }
        if !any_hole && !member {
            return Ok(None);
        }
        let pad = "  ".repeat(depth);
        let base = env.len();
        let mut out = String::new();
        let mut registered = 0;
        let mut registered_fns = 0;
        for (i, b) in bound.into_iter().enumerate() {
            match b {
                Bound::Erased => env.push(true),
                Bound::Value(value) => {
                    let _ = writeln!(out, "{pad}const {} = {value};", var(base + i));
                    env.push(false);
                }
                Bound::Hole(passed) => {
                    // The values are computed now, as the call's arguments
                    // would have been; the next turn is passed them.
                    let mut named = Vec::new();
                    for (level, value) in passed {
                        let name = format!("p{}_{level}$", call.fresh());
                        let _ = writeln!(out, "{pad}const {name} = {value};");
                        named.push((level, name));
                    }
                    self.holes.borrow_mut().push((base + i, named));
                    registered += 1;
                    env.push(false);
                }
                Bound::FnHole(params, body, site) => {
                    // Nothing to compute: the function is only applied.
                    self.fn_holes.borrow_mut().push(FnHole {
                        level: base + i,
                        params,
                        body,
                        site,
                    });
                    registered_fns += 1;
                    env.push(false);
                }
            }
        }
        call.inlining.set(call.inlining.get() + 1);
        call.inlined.borrow_mut().push(id);
        let result = self.tree(&tree, env, depth, Some(call));
        call.inlined.borrow_mut().pop();
        call.inlining.set(call.inlining.get() - 1);
        env.truncate(base);
        let mut holes = self.holes.borrow_mut();
        let keep = holes.len() - registered;
        holes.truncate(keep);
        drop(holes);
        let mut fn_holes = self.fn_holes.borrow_mut();
        let keep = fn_holes.len() - registered_fns;
        fn_holes.truncate(keep);
        drop(fn_holes);
        out.push_str(&result?);
        Ok(Some(out))
    }

    /// If `arg` is `x1 … xk => body`, where `body` is a call to `call`'s
    /// definition with all its arguments, the parameters' names and the
    /// body ([`Gen::fn_holes`]).
    pub(crate) fn fn_hole_arg(
        &self,
        arg: &Term,
        call: &SelfCall,
    ) -> Option<(Vec<stitchwort_core::Name>, Term)> {
        let mut params = Vec::new();
        let mut body = arg.strip_loc();
        while let Term::Lam(name, _, inner, _) = body {
            params.push(name.clone());
            body = inner.strip_loc();
        }
        let (head, args) = body.spine();
        (!params.is_empty() && matches!(head, Term::Def(id) if self.is_self(call, *id, &args)))
            .then(|| (params, body.clone()))
    }

    /// Whether variable `level` stands for a function whose body is a call
    /// to the definition itself ([`Gen::fn_holes`]).
    pub(crate) fn is_fn_hole(&self, level: usize) -> bool {
        self.fn_holes.borrow().iter().any(|h| h.level == level)
    }

    /// If `term`, in an environment of `depth` variables, applies a
    /// function that stands for a call to the definition itself
    /// ([`Gen::fn_holes`]) to all its parameters, or is a constructor with
    /// such an application as a field: the term with the function's body
    /// in place of the application, under `let`s that bind its parameters
    /// to the arguments, in order (so they're computed as the arguments
    /// would have been). A parameter the body doesn't use isn't computed,
    /// as for any `let` whose variable is unused.
    pub(crate) fn apply_fn_hole(&self, term: &Term, depth: usize) -> Fallible<Option<Term>> {
        let holes = self.fn_holes.borrow();
        if holes.is_empty() {
            return Ok(None);
        }
        let applied = |t: &Term| -> Option<(usize, Vec<Term>)> {
            let (head, args) = t.strip_loc().spine();
            let Term::Var(ix) = head.strip_loc() else {
                return None;
            };
            let level = depth.checked_sub(ix + 1)?;
            let h = holes.iter().rposition(|h| h.level == level)?;
            (holes[h].params.len() == args.len()).then(|| (h, args.into_iter().cloned().collect()))
        };
        // The body, under the parameters, moved from its own environment
        // to this one.
        let body_here = |h: &FnHole| h.body.shift(self.g, depth - h.site, h.params.len());
        let (h, args, inner) = if let Some((h, args)) = applied(term) {
            let inner = body_here(&holes[h])?;
            (h, args, inner)
        } else if let Term::Ctor(d, c, fields) = term.strip_loc() {
            let found: Vec<_> = fields
                .iter()
                .enumerate()
                .filter_map(|(i, f)| applied(f).map(|a| (i, a)))
                .collect();
            let [(at, (h, args))] = found.as_slice() else {
                return Ok(None);
            };
            let k = holes[*h].params.len();
            let mut moved = Vec::new();
            for (i, f) in fields.iter().enumerate() {
                moved.push(Rc::new(if i == *at {
                    body_here(&holes[*h])?
                } else {
                    f.shift(self.g, k, 0)?
                }));
            }
            (*h, args.clone(), Term::Ctor(*d, *c, moved))
        } else {
            return Ok(None);
        };
        let params = &holes[h].params;
        let mut out = inner;
        for (j, (name, arg)) in params.iter().zip(&args).enumerate().rev() {
            let unused = !out.mentions(0);
            out = Term::Let(
                name.clone(),
                Rc::new(Term::Sort(Sort::Prop)),
                Rc::new(arg.shift(self.g, j, 0)?),
                Rc::new(out),
                unused,
                ProofMark::Unknown,
            );
        }
        Ok(Some(out))
    }

    /// A lambda applied where it's made, `(x1 … xk => body) a1 … ak rest…`,
    /// as `let x1 := a1; …; let xk := ak; body rest…`, so that it's
    /// generated as `let`s ([`Gen::inline_let`], [`Gen::function_body`]),
    /// not as a closure made and called on the spot. The elaborator writes
    /// `a == b` and `x ∈ xs` that way, with the operands bound
    /// (`(a => holds (decEq a b)) x`, elab's `bind.rs`), so inside a
    /// callback the closure would be made once for each element. Each `let`
    /// computes its argument before the body, as the call would have; one
    /// the body doesn't use isn't computed.
    pub(crate) fn beta_lets(&self, head: &Term, args: &[&Term]) -> Fallible<Option<Term>> {
        let mut head = head;
        while let Term::Loc(_, t) | Term::Ann(t, _) = head {
            head = t;
        }
        let mut names = Vec::new();
        let mut body = head;
        while names.len() < args.len()
            && let Term::Lam(x, _, inner, _) = body
        {
            names.push(x.clone());
            body = inner.strip_loc();
        }
        let k = names.len();
        if k == 0 {
            return Ok(None);
        }
        let mut out = body.clone();
        for arg in &args[k..] {
            out = Term::app(out, arg.shift(self.g, k, 0)?);
        }
        for (j, name) in names.into_iter().enumerate().rev() {
            let unused = !out.mentions(0);
            out = Term::Let(
                name,
                Rc::new(Term::Sort(Sort::Prop)),
                Rc::new(args[j].shift(self.g, j, 0)?),
                Rc::new(out),
                unused,
                ProofMark::Unknown,
            );
        }
        Ok(Some(out))
    }

    /// The body of `let x := value; body` with `value` in place of `x`, if
    /// that computes `value` no more often than the `let` does: `value` is
    /// a variable or a number, or `x` is used at most once, and not inside
    /// a lambda ([`single_use`]). It may then be computed later than the
    /// `let` would have, or not at all, which is fine: generated code is
    /// pure and total (a computation with effects is a value until it's
    /// run), so when it's computed doesn't matter (see `def_ref`).
    pub(crate) fn inline_let(&self, value: &Term, body: &Term) -> Fallible<Option<Term>> {
        let inline = match value.strip_loc() {
            Term::Var(_) => true,
            Term::Nat(_) => !scrutinised(body),
            _ => single_use(self, body),
        };
        Ok(if inline {
            Some(body.instantiate(self.g, value)?)
        } else {
            None
        })
    }

    /// `term`'s JS as an arrow function's body (in `env`, which has the
    /// function's parameters). Leading `let`s that aren't inlined
    /// ([`Gen::inline_let`]) are `const`s in a block, `{ const v3 = …;
    /// return …; }`, rather than a closure made and called each time the
    /// function is: computed once, in order, before the rest.
    pub(crate) fn function_body(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        let start = env.len();
        let mut statements = String::new();
        let body = self.function_statements(term, env, &mut statements);
        env.truncate(start);
        let body = body?;
        Ok(if !statements.is_empty() {
            format!("{{ {statements}return {body}; }}")
        } else if body.starts_with('{') {
            // An object literal as an arrow function's body needs
            // parentheses, or it's read as a block.
            format!("({body})")
        } else {
            body
        })
    }

    /// [`Gen::function_body`]'s `const`s, added to `statements`, and the
    /// expression after them.
    pub(crate) fn function_statements(
        &self,
        term: &Term,
        env: &mut Vec<bool>,
        statements: &mut String,
    ) -> Fallible<String> {
        let mut term = term.clone();
        loop {
            let next = match term.strip_loc() {
                Term::Let(_, _, _, body, true, _) => {
                    env.push(true);
                    (**body).clone()
                }
                Term::Let(_, _, value, body, false, _) => match self.inline_let(value, body)? {
                    Some(inlined) => inlined,
                    None => {
                        let value = self.expr(value, env)?;
                        let _ = write!(statements, "const {} = {value}; ", var(env.len()));
                        env.push(false);
                        (**body).clone()
                    }
                },
                Term::Ann(inner, _) => (**inner).clone(),
                Term::App(..) => {
                    let (head, args) = term.spine();
                    match self.beta_lets(head, &args)? {
                        Some(lets) => lets,
                        None => return self.expr(&term, env),
                    }
                }
                _ => return self.expr(&term, env),
            };
            term = next;
        }
    }
}

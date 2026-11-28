use super::*;

impl<'g> Gen<'g> {
    pub(crate) fn expr(&self, term: &Term, env: &mut Vec<bool>) -> Fallible<String> {
        self.g.machine.budget.nesting(PASS)?;
        Ok(match term {
            Term::Loc(_, t) | Term::Ann(t, _) => self.expr(t, env)?,
            Term::Var(ix) => {
                let level = env.len() - 1 - ix;
                if self.hole_at(level).is_some() || self.is_fn_hole(level) {
                    self.hole_misused.set(true);
                }
                if env[level] {
                    "undefined".into()
                } else {
                    var(level)
                }
            }
            Term::Def(id) => self.def_ref(*id, &[], env)?,
            Term::Nat(n) if self.nat.is_some() => format!("{n}n"),
            Term::Nat(n) => self.nat_from_number(n),
            // A compact list of characters (a text literal's): the cons list
            // it stands for, built from a string in a loop.
            Term::Chars(chars) => {
                let text: String = chars.as_slice().iter().collect();
                format!("charsOfText({})", js_string_literal(&text))
            }
            Term::App(..) => {
                let (head, args) = term.spine();
                if let Term::Def(id) = head {
                    return self.def_ref(*id, &args, env);
                }
                if let Some(reduced) = stitchwort_rt::erasure::beta_variable(self.g, head, &args)? {
                    return self.expr(&reduced, env);
                }
                if let Some(lets) = self.beta_lets(head, &args)? {
                    return self.expr(&lets, env);
                }
                let head = self.expr(head, env)?;
                // An erased function (a proof parameter) applied to
                // anything is erased too.
                if head == "undefined" {
                    return Ok(head);
                }
                let mut out = format!("({head})");
                for arg in args {
                    let _ = write!(out, "({})", self.expr(arg, env)?);
                }
                out
            }
            Term::Lam(_, _, body, _)
                if self.run_delay && stitchwort_rt::erasure::is_done_continuation(self.g, body) =>
            {
                run::DONE_K.into()
            }
            Term::Lam(_, _, body, _) => {
                let level = env.len();
                env.push(false);
                let body = self.function_body(body, env);
                env.pop();
                format!("(({}) => {})", var(level), body?)
            }
            // A skipped `let` (a proof, a type, or unused) emits nothing: its
            // variable is `undefined`, as an erased parameter's is.
            Term::Let(_, _, _, body, true, _) => {
                env.push(true);
                let body = self.expr(body, env);
                env.pop();
                body?
            }
            // In an expression, computed once, before the body. (In a case
            // tree's leaf, it's a `const`: `Gen::let_statement`.)
            Term::Let(_, _, value, body, false, _) => {
                if let Some(inlined) = self.inline_let(value, body)? {
                    return self.expr(&inlined, env);
                }
                let value = self.expr(value, env)?;
                let level = env.len();
                env.push(false);
                let body = self.expr(body, env)?;
                env.pop();
                if body.starts_with('{') {
                    format!("(({}) => ({body}))({value})", var(level))
                } else {
                    format!("(({}) => {body})({value})", var(level))
                }
            }
            Term::Ctor(d, c, args) => {
                let data = self.g.data(*d);
                if data.sort() == Sort::Prop {
                    return Ok("undefined".into());
                }
                if Some(*d) == self.text {
                    // A string: a literal if the characters are, otherwise
                    // made from the list in a loop.
                    return Ok(match text_literal(&args[0]) {
                        Some(text) => js_string_literal(&text),
                        None => format!("textOfChars({})", self.expr(&args[0], env)?),
                    });
                }
                if Some(*d) == self.array {
                    let field = data
                        .unboxed_field()
                        .expect("an array is a record of one field");
                    return Ok(format!("arrayOfList({})", self.expr(&args[field], env)?));
                }
                if Some(*d) == self.nat {
                    // Count the `Succ`s: `Succ (Succ x)` is `x + 2n`, and a
                    // literal is just a number.
                    let mut count = 0u64;
                    let mut inner = term;
                    while let Term::Ctor(_, 1, succ) = inner.strip_loc() {
                        count += 1;
                        inner = &succ[0];
                    }
                    return Ok(match (inner.strip_loc(), count) {
                        (Term::Ctor(_, 0, _), n) => format!("{n}n"),
                        (Term::Nat(k), n) => format!("{}n", &**k + n),
                        (_, n) => format!("({} + {n}n)", self.expr(inner, env)?),
                    });
                }
                if Some(*d) == self.float {
                    // A `number`: a literal from the bits if they're known
                    // (never the source's spelling, docs/proposals/float.md
                    // §2.3), otherwise the double they encode.
                    return Ok(
                        match self
                            .nat_literal(&args[0])
                            .and_then(|b| u64::try_from(b).ok())
                        {
                            Some(bits) => float_literal_js(bits),
                            None => format!("fromCanonicalBits({})", self.expr(&args[0], env)?),
                        },
                    );
                }
                if Some(*d) == self.int {
                    // `OfNat n` is `n`, and `NegSucc n` is `-n - 1n`. A
                    // `Nat`'s JS is a literal, a name, a call or in brackets,
                    // so `-` applies to all of it.
                    return Ok(match (*c, self.nat_literal(&args[0])) {
                        (0, _) => self.expr(&args[0], env)?,
                        (_, Some(n)) => format!("-{}n", n + 1u32),
                        (_, None) => format!("(-{} - 1n)", self.expr(&args[0], env)?),
                    });
                }
                // A record with one run-time field is that field (D866).
                if let Some(i) = self.unboxed(*d) {
                    return self.expr(&args[i], env);
                }
                let ctor = &data.ctors()[*c];
                let mut fields = Vec::new();
                if !data.record() {
                    fields.push(format!("tag: \"{}\"", ctor.name));
                }
                for (f, (erased, arg)) in ctor.field_erased.iter().zip(args).enumerate() {
                    if !erased {
                        let key = ts_key(&field_key_at(self.g, *d, *c, f));
                        fields.push(format!("{key}: {}", self.expr(arg, env)?));
                    }
                }
                if fields.is_empty() {
                    "{}".into()
                } else {
                    format!("{{ {} }}", fields.join(", "))
                }
            }
            // Proofs are erased, and transport along an equality does nothing.
            Term::J(_, base, _, _) => self.expr(base, env)?,
            // A field, read as a `match` on the record reads it.
            Term::Proj(d, i, t) => {
                if self.g.data(*d).ctors()[0].field_erased[*i] {
                    "undefined".into()
                } else {
                    let x = self.expr(t, env)?;
                    if Some(*d) == self.float {
                        format!("toCanonicalBits({x})")
                    } else if Some(*d) == self.array {
                        // A version array: its `toList` is built, as a
                        // `match` on it builds it.
                        format!("listOfArray({x})")
                    } else if self.unboxed(*d).is_some() {
                        x
                    } else {
                        format!("({x}){}", member(&field_key_at(self.g, *d, 0, *i)))
                    }
                }
            }
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Quot(QuotForm::Type, ..) => "undefined".into(),
            // Quotients (docs/proposals/map-equality.md §7.4.1, D921), as in
            // the Rust runtime: `Quot.mk a` is `a` (`undefined` when the
            // carrier's elements are erased), a lift whose result isn't
            // erased is the application `f q` (§7.4.2), and the rest are
            // proofs or types.
            Term::Quot(QuotForm::Mk, args, false, _) => self.expr(&args[2], env)?,
            Term::Quot(QuotForm::Lift, args, false, _) => {
                let f_q = Term::App(args[3].clone(), args[5].clone(), Icit::Explicit);
                self.expr(&f_q, env)?
            }
            Term::Quot(QuotForm::Mk | QuotForm::Lift | QuotForm::Ind | QuotForm::Sound, ..) => {
                "undefined".into()
            }
            Term::Case(..) | Term::NumCase(..) => {
                return Err(internal("case outside a case tree"));
            }
            Term::Meta(_) => {
                return Err(internal("unsolved metavariable in a checked definition"));
            }
        })
    }

    /// A call to a definition, leaving out its erased arguments.
    pub(crate) fn def_ref(
        &self,
        id: DefId,
        args: &[&Term],
        env: &mut Vec<bool>,
    ) -> Fallible<String> {
        if !args.is_empty() {
            let arity = self.g.def(id).arity();
            if args.len() >= arity
                && !self.empty_call(id, args)
                && let Some((f, passed)) = self.forwarder(id)
            {
                let mut same = args[f].clone();
                for k in passed {
                    same = Term::app(same, args[k].clone());
                }
                for arg in &args[arity..] {
                    same = Term::app(same, (*arg).clone());
                }
                return self.expr(&same, env);
            }
            if let Some(f) = self.known_function(id) {
                return self.def_ref(f, args, env);
            }
        }
        // A closed signature map (a `translate`'s, say): built at its first
        // use and kept in a module variable, not built again on every call
        // (stitchwort_rt::hoist). Generated code is pure and total, so when
        // it's built doesn't matter, and the first use builds it exactly
        // where the code did before.
        if !self.hoisting.get()
            && let Some(sig_maps) = &self.sig_maps
            && sig_maps.closed_map(self.g, id, args)
        {
            self.hoisting.set(true);
            let value = self.def_call(id, args, env);
            self.hoisting.set(false);
            let value = value?;
            let mut hoisted = self.hoisted.borrow_mut();
            let i = match hoisted.iter().position(|v| *v == value) {
                Some(i) => i,
                None => {
                    hoisted.push(value.clone());
                    hoisted.len() - 1
                }
            };
            return Ok(format!("(sigmap${i} ??= {value})"));
        }
        self.def_call(id, args, env)
    }

    /// The declarations of the module variables that hold the closed
    /// signature maps, if there are any: `var`s, so that a use earlier in
    /// the module (any use, since the definitions come first) is fine.
    pub(crate) fn hoisted_vars(&self) -> String {
        let mut out = String::new();
        let n = self.hoisted.borrow().len();
        if n > 0 {
            let names: Vec<String> = (0..n).map(|i| format!("sigmap${i}")).collect();
            let _ = write!(
                out,
                "\n// Closed signature maps, each built at its first use.\nvar {};\n",
                names.join(", ")
            );
        }
        let curried = self.curried.borrow();
        if !curried.is_empty() {
            let _ = write!(
                out,
                "\n// Definitions used as values, taking their arguments one at a time, each\n\
                 // made at its first use.\nvar {};\n",
                curried.join(", ")
            );
        }
        out
    }

    /// The comparison of `instance`, an `Ord` instance, if it's a definition
    /// whose own body says which: a record of the fields
    /// (`{ compare = Nat.compare, … }`) or `Ord.fromCompare c …`, with the
    /// comparison a definition. So `Ord.compare Text.instOrd x y` (a derived
    /// `Ord` on a record over `Text` is this) is `Text.compare x y`, a direct
    /// call, rather than a read of the dictionary's field and a call of the
    /// closure there one argument at a time.
    pub(crate) fn known_compare(&self, instance: &Term) -> Option<Rc<Term>> {
        let Term::Def(id) = instance.strip_loc() else {
            return None;
        };
        let def = self.g.def(*id);
        if def.arity() != 0 {
            return None;
        }
        let body = def.run_body()?.strip_loc();
        // The field `compare` of a record built by `Ord`'s constructor.
        let field = |term: &Term| -> Option<Rc<Term>> {
            let Term::Ctor(d, 0, fields) = term.strip_loc() else {
                return None;
            };
            let data = self.g.data(*d);
            let k = data.ctors()[0]
                .fields
                .iter()
                .position(|(name, _)| &**name == "compare")?;
            Some(fields[k].clone())
        };
        let compare = if let Some(compare) = field(body) {
            compare
        } else {
            let (head, args) = body.spine();
            let Term::Def(from) = head.strip_loc() else {
                return None;
            };
            if Some(*from) != self.ord_from_compare {
                return None;
            }
            // `Ord.fromCompare`'s record names its parameter `compare`: the
            // argument in that place.
            let from = self.g.def(*from);
            let mut inner = from.run_body()?.strip_loc();
            for _ in 0..from.arity() {
                let Term::Lam(_, _, b, _) = inner else {
                    return None;
                };
                inner = b.strip_loc();
            }
            let Term::Var(ix) = field(inner)?.strip_loc().clone() else {
                return None;
            };
            let param = from.arity().checked_sub(ix + 1)?;
            Rc::new((*args.get(param)?).clone())
        };
        matches!(compare.strip_loc(), Term::Def(_)).then_some(compare)
    }

    /// `if c then a else b` (`Bool.ifThenElse c (_ => a) (_ => b)`) or
    /// `if h: p then a else b` (`Decidable.elim d (h => a) (h => b)`): the
    /// condition, the bodies of the branches (whose parameter is a proof,
    /// so erased), and the tag of the constructor that takes the first.
    pub(crate) fn conditional<'t>(
        &self,
        id: DefId,
        args: &[&'t Term],
    ) -> Option<(&'t Term, &'t Term, &'t Term, String)> {
        let (cond, then, otherwise, tag) = if Some(id) == self.if_then_else
            && let [_, cond, then, otherwise] = args
        {
            (*cond, *then, *otherwise, "True".to_string())
        } else if Some(id) == self.elim_dec
            && let [_, _, cond, then, otherwise] = args
        {
            (*cond, *then, *otherwise, self.decision_yes_tag())
        } else {
            return None;
        };
        match (then.strip_loc(), otherwise.strip_loc()) {
            (Term::Lam(_, _, then, _), Term::Lam(_, _, otherwise, _)) => {
                Some((cond, then, otherwise, tag))
            }
            _ => None,
        }
    }

    /// Whether a call of `id` with `args` arguments is worth replacing by the
    /// definition's body: a fully applied definition whose result is a
    /// `Decidable p`, whose body is one expression that builds the record
    /// (which is stored as its test). Matching the result type rather than
    /// the names keeps this working when the library's names change; other
    /// decisions (`Bool.decEq`'s case tree, say) keep their calls, because
    /// [`Gen::unfold`] refuses a body that matches on a parameter.
    pub(crate) fn unfolds_decision(&self, id: DefId, args: usize) -> bool {
        let def = self.g.def(id);
        self.result_is_decidable(id)
            && args >= def.arity()
            && !self.is_native(id)
            && self.builds_decision(id)
    }

    /// Whether `id`'s run-time body, under its parameters, is a decision
    /// record built here rather than a case tree or a call. Restricting
    /// unfolding to those keeps a recursive decision from unfolding into
    /// itself forever (the case trees are already refused, by
    /// [`scrutinised`]).
    pub(crate) fn builds_decision(&self, id: DefId) -> bool {
        let Some(decidable) = self.decidable else {
            return false;
        };
        let Some(body) = self.g.def(id).run_body() else {
            return false;
        };
        let mut body = body.strip_loc();
        for _ in 0..self.g.def(id).arity() {
            let Term::Lam(_, _, inner, _) = body else {
                return false;
            };
            body = inner.strip_loc();
        }
        matches!(body, Term::Ctor(d, _, _) if *d == decidable)
    }

    /// Whether `id`'s type ends in `Decidable p`.
    pub(crate) fn result_is_decidable(&self, id: DefId) -> bool {
        let Some(decidable) = self.decidable else {
            return false;
        };
        let mut ty = self.g.def(id).ty().strip_loc();
        while let Term::Pi(_, _, _, codomain, _) = ty {
            ty = codomain.strip_loc();
        }
        matches!(ty, Term::Data(d, _) if *d == decidable)
    }

    /// How a call of `id` with `args` is generated: as a conditional built
    /// from the arguments ([`Gen::conditional`]), as the unfolded body
    /// ([`Gen::unfolds_decision`]), or as a call. This is what reachability
    /// must assume, so that a definition no call remains of isn't generated
    /// ([`specialise::reachable_inlining`]).
    pub(crate) fn inlined(&self, id: DefId, args: &[&Term]) -> Fallible<specialise::Inlined> {
        if Some(id) == self.bool_not && args.len() == 1 {
            return Ok(specialise::Inlined::Args);
        }
        if self.conditional(id, args).is_some() {
            return Ok(specialise::Inlined::Args);
        }
        if self.unfolds_decision(id, args.len())
            && let Some(head) = self.g.def(id).run_body()
            && self.unfold(head, id, args)?.is_some()
        {
            return Ok(specialise::Inlined::Body);
        }
        Ok(specialise::Inlined::No)
    }

    /// The body of the definition `id`, whose run-time `body` is a lambda
    /// per parameter, with `args` in place of the parameters (and any
    /// arguments beyond them applied to it). None unless each parameter is
    /// used at most once and never matched on, so that no argument is
    /// computed twice or has to be a variable. An argument is then computed
    /// where the body uses it, in a branch if that's where it is.
    pub(crate) fn unfold(&self, body: &Term, id: DefId, args: &[&Term]) -> Fallible<Option<Term>> {
        let arity = self.g.def(id).arity();
        let mut out = body;
        for _ in 0..arity {
            let Term::Lam(_, _, inner, _) = out.strip_loc() else {
                return Ok(None);
            };
            out = inner;
        }
        // What the body is at run time: a decision is its test, so its
        // proofs and `holds` are gone, and a parameter is not matched on.
        let mut out = out.rewrite_up(self.g, &mut |t| Ok(self.passed_through(t)))?;
        for j in (0..arity).rev() {
            let uses = out
                .subterms()
                .filter(|(t, binders)| matches!(t, Term::Var(ix) if *ix == *binders))
                .count();
            if uses > 1 || scrutinised(&out) {
                return Ok(None);
            }
            out = out.instantiate(self.g, &args[j].shift(self.g, j, 0)?)?;
        }
        for arg in &args[arity..] {
            out = Term::app(out, (*arg).clone());
        }
        Ok(Some(out))
    }

    /// [`Gen::def_ref`], without building a closed map once.
    fn def_call(&self, id: DefId, args: &[&Term], env: &mut Vec<bool>) -> Fallible<String> {
        // In an expression, a conditional, with no closures for the branches.
        if let Some((cond, then, otherwise, tag)) = self.conditional(id, args) {
            let cond = self.expr(cond, env)?;
            // The branches' parameter is a proof, so it's erased.
            let mut branch = |body: &Term| -> Fallible<String> {
                env.push(true);
                let out = self.expr(body, env);
                env.pop();
                out
            };
            let then = branch(then)?;
            let otherwise = branch(otherwise)?;
            return Ok(format!(
                "({cond}.tag === {} ? {then} : {otherwise})",
                js_string_literal(&tag)
            ));
        }
        // `Bool.not b` is the opposite test, so `!` on `b`'s tag: no call
        // remains to the definition (whose body switches on the tag).
        if Some(id) == self.bool_not
            && let [b] = args
        {
            let b = self.expr(b, env)?;
            return Ok(format!(
                "({{ tag: !(({b}).tag === \"True\") ? \"True\" : \"False\" }})"
            ));
        }
        // A decision combinator's body is a conditional on its operands'
        // tests, so a call is that conditional, not a call of a helper that
        // takes the second operand as a closure.
        if self.unfolds_decision(id, args.len())
            && let Some(head) = self.g.def(id).run_body()
            && let Some(unfolded) = self.unfold(head, id, args)?
        {
            return self.expr(&unfolded, env);
        }
        if Some(id) == self.ord_compare
            && let [_, instance, rest @ ..] = args
            && let Some(compare) = self.known_compare(instance)
            && let Term::Def(compare) = compare.strip_loc()
        {
            return self.def_ref(*compare, rest, env);
        }
        // A partial computation is the token, whatever its arguments: they
        // only feed a `Delay`, which nothing can run, so they aren't
        // computed.
        if let Some(mask) = &self.info(id)?.delay {
            let mut out = "delayed".to_string();
            for erased in mask.iter().skip(args.len()).rev() {
                if !erased {
                    out = format!("((_) => {out})");
                }
            }
            return Ok(out);
        }
        // A state-passing handler at the empty row: its fold runs as a loop
        // with the state in a variable (docs/proposals/effect-runtime.md
        // §9.1.5, stage 4d).
        if let Some(effect) = &self.effect
            && effect.is_fold(id)
            && let Some(fused) = effect.fuse(self.g, args)?
        {
            // `fuse` needs the computation, the seventh argument; any after
            // it are the result's (the state).
            let mut out = format!(
                "effFoldState({}, {}, {}, {})",
                fused.comp,
                self.expr(&fused.done, env)?,
                self.expr(&fused.call, env)?,
                self.expr(args[6], env)?
            );
            for arg in &args[7..] {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
            return Ok(out);
        }
        // A call at the empty row calls the variant, which takes no row.
        let variant = self.empty_call(id, args);
        let info = if variant {
            self.empty_info(id)?
        } else {
            self.info(id)?
        };
        let mask = &info.mask;
        let mut out = match info.convention {
            Convention::Erased => return Ok("undefined".into()),
            Convention::Thunk => format!("{}()", self.js_name(id, variant)),
            Convention::Value | Convention::Function => self.js_name(id, variant),
        };
        // Values the callee is passed before the call's own arguments.
        let mut prefix = Vec::new();
        // A `handle`'s fold: lazy resumption where its carrier (the fourth
        // argument, erased) is a computation (docs/proposals/effect-runtime.md
        // §9.2). The same parameters, so the call is built the same way.
        if let Some(effect) = &self.effect
            && effect.is_fold(id)
            && let Some(carrier) = args.get(3)
        {
            match effect.carrier(carrier) {
                effect::Carrier::Tree => out = "effFoldCompLazy".into(),
                effect::Carrier::Row(row) => {
                    let row = self.expr(row, env)?;
                    if row != "undefined" {
                        out = "effFoldCompIn".into();
                        prefix.push(row);
                    }
                }
                effect::Carrier::Value => {}
            }
        }
        if info.uncurried {
            return self.uncurried_call(out, prefix, mask, args, env);
        }
        debug_assert!(prefix.is_empty(), "only an uncurried fold is passed a row");
        // Used as a value with an erased parameter still unsupplied: the
        // receiver knows only the type, so it passes the type and proof
        // arguments too. A closure over all the remaining parameters takes
        // them and ignores the erased ones (D922). The supplied arguments
        // are computed once, outside it (`$s{i}`), not on every call.
        let closure = args.len() < mask.len() && mask[args.len()..].iter().any(|erased| *erased);
        let mut bound = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            if !mask.get(i).copied().unwrap_or(false) {
                let value = self.expr(arg, env)?;
                if closure && !is_simple(&value) {
                    let _ = write!(out, "($s{i})");
                    bound.push((format!("$s{i}"), value));
                } else {
                    let _ = write!(out, "({value})");
                }
            }
        }
        if closure {
            for (i, erased) in mask.iter().enumerate().skip(args.len()) {
                if !erased {
                    let _ = write!(out, "($p{i})");
                }
            }
            for (i, erased) in mask.iter().enumerate().skip(args.len()).rev() {
                out = if *erased {
                    format!("((_) => {out})")
                } else {
                    format!("(($p{i}) => {out})")
                };
            }
            out = bind_supplied(out, bound);
        }
        Ok(out)
    }

    /// A use of `head`, a definition whose JS takes all its runtime
    /// arguments in one call (D1173), with `prefix` passed first, and then
    /// `args`, whose erasure `mask` gives up to its arity:
    ///
    /// - with all of them, one call, `f(a, b)`, and any beyond its arity
    ///   applied to the result one at a time, `f(a, b)(c)`;
    /// - with fewer, a closure that takes the rest one at a time, as any
    ///   function value does, the erased ones too if any remains (D922):
    ///   `(($p1) => f(a, $p1))`. The supplied arguments are computed once,
    ///   outside it (`$s{i}`). With none supplied but erased ones, the
    ///   closure is the same everywhere: it's made once, at its first use,
    ///   and kept in a module variable (`f$c`).
    pub(crate) fn uncurried_call(
        &self,
        head: String,
        prefix: Vec<String>,
        mask: &[bool],
        args: &[&Term],
        env: &mut Vec<bool>,
    ) -> Fallible<String> {
        if args.len() >= mask.len() {
            let mut values = prefix;
            for (arg, erased) in args.iter().zip(mask) {
                if !erased {
                    values.push(self.expr(arg, env)?);
                }
            }
            let mut out = format!("{head}({})", values.join(", "));
            for arg in &args[mask.len()..] {
                let _ = write!(out, "({})", self.expr(arg, env)?);
            }
            return Ok(out);
        }
        let mut bound = Vec::new();
        let mut values = Vec::new();
        for (j, value) in prefix.into_iter().enumerate() {
            if is_simple(&value) {
                values.push(value);
            } else {
                values.push(format!("$r{j}"));
                bound.push((format!("$r{j}"), value));
            }
        }
        let closed = values.is_empty() && mask[..args.len()].iter().all(|erased| *erased);
        for (i, (arg, erased)) in args.iter().zip(mask).enumerate() {
            if !erased {
                let value = self.expr(arg, env)?;
                if is_simple(&value) {
                    values.push(value);
                } else {
                    values.push(format!("$s{i}"));
                    bound.push((format!("$s{i}"), value));
                }
            }
        }
        for (i, erased) in mask.iter().enumerate().skip(args.len()) {
            if !erased {
                values.push(format!("$p{i}"));
            }
        }
        let mut out = format!("{head}({})", values.join(", "));
        for (i, erased) in mask.iter().enumerate().skip(args.len()).rev() {
            out = if *erased {
                format!("(_) => {out}")
            } else {
                format!("($p{i}) => {out}")
            };
        }
        // The common use as a value: a polymorphic function with its type
        // arguments, `List.map {A} {B}`, passed on.
        if closed && mask[args.len()..].iter().all(|erased| !erased) {
            let name = format!("{head}$c");
            let mut curried = self.curried.borrow_mut();
            if !curried.contains(&name) {
                curried.push(name.clone());
            }
            return Ok(format!("({name} ??= {out})"));
        }
        Ok(bind_supplied(format!("({out})"), bound))
    }

    /// `function $$f(…)`, exported as `f`: decode the inputs, run the
    /// precondition checks, call the compiled definition, encode the result.
    /// Running out of stack on the way is a `StitchwortResourceError`.
    /// Parameter `i` (counting all parameters) is `arg{i}`, decoded as
    /// `v{i}`, which is what the compiled checks refer to.
    pub(crate) fn wrapper(&self, sig: &ExportSig) -> Fallible<String> {
        let params: Vec<String> = sig.param_positions.iter().map(|p| arg(*p)).collect();
        let mut out = format!(
            "\nfunction {}({}) {{\n  try {{\n",
            wrapper_name(&sig.name),
            params.join(", ")
        );
        let mut call = def_name(self.g.def(sig.id).path());
        let info = self.info(sig.id)?;
        if info.convention == Convention::Thunk {
            call.push_str("()");
        }
        // An uncurried definition takes the parameters up to its arity in
        // one call (D1173); any after them are its result's.
        let mut together = Vec::new();
        let mut apart = String::new();
        for ((x, b), position) in sig.params.iter().zip(&sig.param_positions) {
            let _ = writeln!(
                out,
                "    const {} = decodeFast({}, {}, {}, \"{x}\");",
                var(*position),
                self.fast_decoder(b),
                self.type_const(b),
                arg(*position)
            );
            if info.uncurried && *position < info.mask.len() {
                together.push(var(*position));
            } else {
                let _ = write!(apart, "({})", var(*position));
            }
        }
        if info.uncurried {
            let _ = write!(call, "({})", together.join(", "));
        }
        call.push_str(&apart);
        let yes = self.decision_yes_tag();
        for check in &sig.checks {
            // Parameters before the check: proofs are erased, data is decoded.
            let mut env: Vec<bool> = (0..check.position)
                .map(|i| !sig.param_positions.contains(&i))
                .collect();
            let decision = self.expr(&check.decision, &mut env)?;
            let message = format!("precondition `{}` doesn't hold", check.description)
                .replace('\\', "\\\\")
                .replace('"', "\\\"");
            let _ = writeln!(
                out,
                "    if ({decision}.tag !== \"{yes}\") {{\n      throw new StitchwortInputError(\"{message}\");\n    }}"
            );
        }
        let _ = writeln!(
            out,
            "    return encodeFast({}, {}, {call});\n  }} catch (e) {{\n    throw outOfResources(\"{}\", e);\n  }}\n}}",
            self.fast_encoder(&sig.result),
            self.type_const(&sig.result),
            sig.name
        );
        Ok(out)
    }

    /// A `Nat` written as a compact number, in the ordinary data-type
    /// representation (when [`nat_data`] doesn't apply): a loop building the
    /// type's constructors. The number representation would just be `{n}n`.
    pub(crate) fn nat_from_number(&self, n: &BigUint) -> String {
        let d = self
            .g
            .env
            .registry()
            .data(Builtin::Nat)
            .expect("a checked `Nat` term has a declared `Nat`");
        let data = self.g.data(d);
        let zero = js_string_literal(&data.ctors()[0].name);
        let succ = js_string_literal(&data.ctors()[1].name);
        let key = ts_key(&field_key_at(self.g, d, 1, 0));
        format!(
            "((k) => {{ let v = {{ tag: {zero} }}; for (let i = 0n; i < k; i++) v = {{ tag: {succ}, {key}: v }}; return v; }})({n}n)"
        )
    }

    /// The number a `Nat` term is, if it's written out: `Succ`s around
    /// `Zero` or a compact number.
    pub(crate) fn nat_literal(&self, term: &Term) -> Option<BigUint> {
        let mut count = 0u64;
        let mut term = term.strip_loc();
        loop {
            match term {
                Term::Nat(k) => return Some(&**k + count),
                Term::Ctor(d, 0, _) if Some(*d) == self.nat => return Some(BigUint::from(count)),
                Term::Ctor(d, 1, succ) if Some(*d) == self.nat => {
                    count += 1;
                    term = succ[0].strip_loc();
                }
                _ => return None,
            }
        }
    }

    /// The runtime's `INT` codec, for the prelude's `Int` `d` (only when
    /// [`bind_int`] binds it). At the boundary, an `Int` is a `bigint` of
    /// either sign. Decoding refuses anything else, including a `number`
    /// and a numeric string; encoding can't fail.
    pub(crate) fn int_codec(&self, d: DataId) -> String {
        const DECODE: &str = "(x) => (typeof x === \"bigint\" ? x : refuse(\"expected a bigint\"))";
        if self.int.is_some() {
            return format!(
                "\n// `Int` is a `bigint` of either sign, inside generated code too.\nconst INT = leaf({DECODE}, (v) => v);\n"
            );
        }
        // Inside generated code, `OfNat n` and `NegSucc n` are objects, as
        // any data type's constructors are (`Options::native_int` off).
        let data = self.g.data(d);
        let tag = |c: usize| js_string_literal(&data.ctors()[c].name);
        let field = |c: usize| key(self.g, d, &data.ctors()[c].fields[0].0);
        format!(
            "\n// `Int` is a `bigint` of either sign at the boundary, and `{of_nat}` or\n\
             // `{neg_succ}` inside generated code.\n\
             const INT = leaf(\n  \
               (x) => {{\n    \
                 const n = ({DECODE})(x);\n    \
                 return n >= 0n ? {{ tag: {t0}, {k0}: n }} : {{ tag: {t1}, {k1}: -n - 1n }};\n  \
               }},\n  \
               (v) => (v.tag === {t0} ? v{m0} : -v{m1} - 1n),\n\
             );\n",
            of_nat = data.ctors()[0].name,
            neg_succ = data.ctors()[1].name,
            t0 = tag(0),
            t1 = tag(1),
            k0 = ts_key(&field(0)),
            k1 = ts_key(&field(1)),
            m0 = member(&field(0)),
            m1 = member(&field(1)),
        )
    }

    /// The runtime's `SAFE_NAT` and `SAFE_INT` codecs, for the library's
    /// `SafeNat` and `SafeInt` (only those that cross, given their data
    /// types). At the boundary each is a `number` that is a whole number
    /// within the bounds the types' proof fields state; inside generated
    /// code it's the `Nat` or `Int` itself, since a record with one run-time
    /// field is stored as that field (D866).
    /// Decoding refuses a `bigint` or anything but a `number`, a fraction,
    /// `NaN`, an infinity and anything out of range (a whole `number` beyond
    /// 2^53 - 1 may already have been rounded, so it can't be trusted), and
    /// reads `-0` as 0. Encoding is exact, as the bounds hold of every value.
    pub(crate) fn safe_codecs(&self, nat: Option<DataId>, int: Option<DataId>) -> String {
        let mut out = String::from(
            "\n// A whole number a `number` holds exactly (the library's `SafeNat` and\n\
             // `SafeInt`), as a `bigint`.\n\
             const safeNumber = (x, lowest) => {\n  \
               if (typeof x === \"number\" && x >= lowest && x <= 9007199254740991 && Number.isInteger(x)) return BigInt(x);\n  \
               if (typeof x !== \"number\") refuse(\"expected a number\");\n  \
               if (!Number.isInteger(x)) refuse(\"expected a whole number\");\n  \
               if (x < lowest || x > 9007199254740991) {\n    \
                 refuse(`expected a whole number from ${lowest} to 9007199254740991`);\n  \
               }\n  \
               return BigInt(x);\n\
             };\n",
        );
        // How the decoded number is stored, and read back: as itself if the
        // record is unboxed (D866), which the library's are, or as its field.
        let field = |d: DataId, value: &str| {
            let data = self.g.data(d);
            if self.unboxed(d) == Some(0) {
                return (value.to_string(), "v".to_string());
            }
            let name = &data.ctors()[0].fields[0].0;
            let k = key(self.g, d, name);
            (
                format!("({{ {}: {value} }})", ts_key(&k)),
                format!("v{}", member(&k)),
            )
        };
        if let Some(d) = nat {
            let (dec, enc) = field(d, "safeNumber(x, 0)");
            let _ = writeln!(
                out,
                "const SAFE_NAT = leaf((x) => {dec}, (v) => Number({enc}));"
            );
        }
        if let Some(d) = int {
            let (dec, enc) = field(d, "INT.dec(safeNumber(x, -9007199254740991))");
            let _ = writeln!(
                out,
                "const SAFE_INT = leaf(\n  (x) => {dec},\n  (v) => Number(INT.enc({enc})),\n);"
            );
        }
        out
    }

    /// How the runtime builds and takes apart a `Map Text V` (only when one
    /// crosses): `fromList` and `toList` are the library's own `Map.fromList`
    /// and `Map.toList`, at `Text`'s order, so a decoded map is made by
    /// inserting its entries, and its ordering invariant holds as it does for
    /// any map; a pair is `MkPair`'s tag and its fields' keys.
    pub(crate) fn map_shape(&self) -> Fallible<String> {
        let g = self.g;
        let registry = &g.env.registry();
        let (pair, ctor) = registry
            .ctor(Builtin::MkPair)
            .expect("a checked program has pairs");
        let at = |b: Builtin| {
            registry
                .loaded_def(b)
                .expect("a map crosses only with the library's `Map` loaded")
        };
        // The type arguments are erased, so any term serves for them.
        let ty = Term::Sort(Sort::Type(0));
        let order = Term::Def(at(Builtin::TextInstOrd));
        let mut env = Vec::new();
        let from_list = self.def_ref(at(Builtin::MapFromList), &[&ty, &ty, &order], &mut env)?;
        let to_list = self.def_ref(at(Builtin::MapToList), &[&ty, &ty, &order], &mut env)?;
        Ok(format!(
            "\n// A map that crosses is built and read by the library's own functions.\n\
             const MAP_SHAPE = {{\n  \
               pair: {}, fst: {}, snd: {},\n  \
               fromList: {from_list},\n  \
               toList: {to_list},\n\
             }};\n",
            js_string_literal(&g.data(pair).ctors()[ctor].name),
            js_string_literal(&field_key_at(g, pair, ctor, 0)),
            js_string_literal(&field_key_at(g, pair, ctor, 1)),
        ))
    }

    /// The tag of a decision that holds. A decision is stored as its test
    /// (`Data::unboxed_field`: its proofs are erased), so this is `True`'s.
    pub(crate) fn decision_yes_tag(&self) -> String {
        match self.g.env.registry().ctor(Builtin::True) {
            Some((d, c)) => self.g.data(d).ctors()[c].name.to_string(),
            None => "True".into(),
        }
    }

    /// A JS expression for a boundary type, as the runtime's `decode` and
    /// `encode` take it.
    pub(crate) fn type_expr(&self, b: &Boundary) -> String {
        match b {
            Boundary::Nat => "NAT".into(),
            Boundary::Int => "INT".into(),
            Boundary::SafeNat => "SAFE_NAT".into(),
            Boundary::SafeInt => "SAFE_INT".into(),
            Boundary::Float => "FLOAT".into(),
            Boundary::Bool => "BOOL".into(),
            Boundary::Text => "TEXT".into(),
            Boundary::Char => "CHAR".into(),
            Boundary::List(elem) => format!("list({})", self.type_expr(elem)),
            Boundary::Array(elem) => format!("array({})", self.type_expr(elem)),
            Boundary::Option(_, inner) => format!("option({})", self.type_expr(inner)),
            Boundary::Map(_, key, value) if **key == Boundary::Text => {
                format!("map({})", self.type_expr(value))
            }
            Boundary::Map(_, key, value) => {
                format!("map({}, {})", self.type_expr(value), self.type_expr(key))
            }
            Boundary::Data(d, args) if args.is_empty() => {
                format!("data({})", info_name(self.g.data(*d).path()))
            }
            Boundary::Data(d, args) => {
                let args: Vec<String> = args.iter().map(|a| self.type_expr(a)).collect();
                format!(
                    "data({}, [{}])",
                    info_name(self.g.data(*d).path()),
                    args.join(", ")
                )
            }
            Boundary::Param(i) => format!("param({i})"),
        }
    }

    /// A data type's constructors, and the keys and types of their fields.
    /// Only names the runtime chose, and `info$`-prefixed ones, are used as
    /// JS names; tags and keys are strings.
    ///
    /// A constructor is `[tag, fields]`, with its tag at the boundary third
    /// when that isn't its name; a field is `[key, type]`, with `true` third
    /// for an optional property, and its key inside generated code fourth
    /// when that isn't its key at the boundary. Both come from the type's
    /// one [`repr`].
    pub(crate) fn define(&self, d: DataId) -> Fallible<String> {
        let data = self.g.data(d);
        let repr = repr(self.g, d);
        let mut out = format!("define({}, [\n", info_name(data.path()));
        for (c, (ctor, fields)) in data.ctors().iter().zip(self.generic_fields(d)).enumerate() {
            let mut entries = Vec::new();
            for ((((_, b), external), i), flag) in fields
                .iter()
                .zip(external_keys(&repr, c))
                .zip(runtime_fields(self.g, d, c))
                .zip(external_optional(&repr, c))
            {
                let internal = field_key_at(self.g, d, c, i);
                let optional = optional_property(self.g, d, c, i, b, flag);
                // A field with a default: a function of the object decoded
                // so far (its earlier fields, by their keys inside), giving
                // the default for a missing property (§5.3).
                let default = self.default_call(d, c, i, &|j| {
                    format!("o{}", member(&field_key_at(self.g, d, c, j)))
                })?;
                let rest = if let Some((reads, call)) = default {
                    let function = if reads.is_empty() {
                        format!("() => {call}")
                    } else {
                        format!("(o) => {{ {reads}return {call}; }}")
                    };
                    format!(", false, {}, {function}", js_string_literal(&internal))
                } else if internal != external {
                    format!(", {optional}, {}", js_string_literal(&internal))
                } else if optional {
                    ", true".to_string()
                } else {
                    String::new()
                };
                entries.push(format!(
                    "[{}, {}{rest}]",
                    js_string_literal(external),
                    self.type_expr(b)
                ));
            }
            let fields = entries;
            let tag = &repr.ctors[c].tag;
            let external = if data.record() || *tag == *ctor.name {
                String::new()
            } else {
                format!(", {}", js_string_literal(tag))
            };
            let _ = writeln!(
                out,
                "  [{}, [{}]{external}],",
                js_string_literal(&ctor.name),
                fields.join(", ")
            );
        }
        out.push(']');
        if repr.string_enum {
            out.push_str(", false, [], true");
        }
        if data.record() {
            out.push_str(", true, [");
            for check in self.field_checks(d)? {
                let _ = write!(out, "\n  {check},");
            }
            out.push_str("\n]");
            // Stored as its one run-time field inside generated code (D866),
            // and with `js.unboxed`, at the boundary too.
            if self.unboxed(d).is_some() {
                out.push_str(", false, true");
                if repr.unboxed {
                    out.push_str(", true");
                }
            }
        }
        out.push_str(");\n");
        Ok(out)
    }

    /// The default of field `i` of constructor `c` of `d`, if it has one,
    /// as a call of its helper (docs/proposals/named-arguments.md §5.3):
    /// statements binding the earlier fields the helper takes, each read by
    /// `read` (given the field's index among all the constructor's fields),
    /// and the call. The type's parameters, and erased fields, are types and
    /// proofs, which the call leaves out.
    pub(crate) fn default_call(
        &self,
        d: DataId,
        c: usize,
        i: usize,
        read: &dyn Fn(usize) -> String,
    ) -> Fallible<Option<(String, String)>> {
        let Some(default) = field_default(self.g, d, c, i) else {
            return Ok(None);
        };
        let data = self.g.data(d);
        let ctor = &data.ctors()[c];
        let np = data.params().len();
        let mut env: Vec<bool> = vec![true; np];
        env.extend(&ctor.field_erased[..i]);
        let n = env.len();
        let mut reads = String::new();
        let mut call = Term::Def(default.helper);
        for &l in &default.captures {
            if !env[l] {
                let _ = write!(reads, "const {} = {}; ", var(l), read(l - np));
            }
            let icit = if l < np {
                Icit::Implicit
            } else {
                Icit::Explicit
            };
            call = Term::app_icit(call, Term::Var(n - 1 - l), icit);
        }
        let call = self.expr(&call, &mut env)?;
        Ok(Some((reads, call)))
    }

    /// For each proof field of record `d` with a decision procedure: the
    /// message for when it doesn't hold, and a function of the decoded
    /// object saying whether it does.
    pub(crate) fn field_checks(&self, d: DataId) -> Fallible<Vec<String>> {
        let data = self.g.data(d);
        let ctor = &data.ctors()[0];
        let np = data.params().len();
        let yes = self.decision_yes_tag();
        let unboxed = self.unboxed(d).is_some();
        let mut out = Vec::new();
        let mut validators: Vec<_> = data.validators().iter().filter(|v| v.ctor == 0).collect();
        validators.sort_by_key(|v| v.field);
        for v in validators {
            // The parameters are types, so erased; the earlier fields are read
            // from the object.
            let mut env: Vec<bool> = vec![true; np];
            let mut reads = String::new();
            for (j, ((field, _), erased)) in ctor.fields[..v.field]
                .iter()
                .zip(&ctor.field_erased)
                .enumerate()
            {
                if !erased && unboxed {
                    // The record is its one run-time field (D866).
                    let _ = write!(reads, "const {} = o; ", var(np + j));
                } else if !erased {
                    let _ = write!(
                        reads,
                        "const {} = o{}; ",
                        var(np + j),
                        member(&key(self.g, d, field))
                    );
                }
                env.push(*erased);
            }
            let decision = self.expr(&v.decision, &mut env)?;
            let mut names: Vec<stitchwort_core::Name> =
                data.params().iter().map(|(x, _)| x.clone()).collect();
            names.extend(ctor.fields[..v.field].iter().map(|(x, _)| x.clone()));
            let field = &ctor.fields[v.field];
            let message = format!(
                "proof field `{}` (`{}`) doesn't hold",
                field.0,
                pretty::term_ascii(self.g, &names, &field.1)
            );
            out.push(format!(
                "[{}, (o) => {{ {reads}return {decision}.tag === \"{yes}\"; }}]",
                js_string_literal(&message)
            ));
        }
        Ok(out)
    }

    /// A function's parameters are `readonly`, so a caller may pass either; its
    /// result, and every list inside a data type's declaration, is a
    /// mutable `T[]`. The codec copies arrays both ways, so a caller who gets
    /// one may keep and change it, and a type an app wrote with `T[]` is
    /// assignable both ways (`readonly T[]` isn't assignable to `T[]`).
    /// `params` names a data type's parameters, inside its alias.
    ///
    /// With `inputs`, the type is an input's (an export's parameter): a data
    /// type in `inputs` is its input shape, `RangeOptionsInput`, with its
    /// defaulted fields optional (docs/proposals/named-arguments.md §5.3,
    /// D1101). Without, it's a result's, where every field is present.
    pub(crate) fn ts_type(
        &self,
        b: &Boundary,
        readonly: bool,
        params: &[String],
        inputs: Inputs,
    ) -> String {
        match b {
            Boundary::Nat | Boundary::Int => "bigint".into(),
            Boundary::SafeNat | Boundary::SafeInt | Boundary::Float => "number".into(),
            Boundary::Bool => "boolean".into(),
            Boundary::Text | Boundary::Char => "string".into(),
            Boundary::Option(..) => {
                format!(
                    "{} | undefined",
                    self.ts_type(&b.payload(), readonly, params, inputs)
                )
            }
            // A dictionary: inputs are read-only, as lists are.
            // A `js.unboxed` key is named: its alias is `string`, which an
            // index signature takes.
            Boundary::Map(_, key, value) => format!(
                "{{ {}[k: {}]: {} }}",
                if readonly { "readonly " } else { "" },
                self.ts_type(key, readonly, params, inputs),
                self.ts_type(value, readonly, params, inputs)
            ),
            // An array crosses as a list does.
            Boundary::Array(elem) => {
                self.ts_type(&Boundary::List(elem.clone()), readonly, params, inputs)
            }
            Boundary::List(elem) if readonly => {
                // `readonly readonly T[][]` isn't TypeScript, and a union
                // needs its parentheses too.
                let text = self.ts_type(elem, true, params, inputs);
                if text.starts_with("readonly ") || matches!(**elem, Boundary::Option(..)) {
                    format!("readonly ({text})[]")
                } else {
                    format!("readonly {text}[]")
                }
            }
            Boundary::List(elem) if matches!(**elem, Boundary::Option(..)) => {
                format!("({})[]", self.ts_type(elem, false, params, inputs))
            }
            Boundary::List(elem) => format!("{}[]", self.ts_type(elem, false, params, inputs)),
            Boundary::Data(d, args) => {
                let mut name = type_name(self.g.data(*d).name());
                if inputs.is_some_and(|set| set.contains(d)) {
                    name.push_str(INPUT_SUFFIX);
                }
                if args.is_empty() {
                    return name;
                }
                let args: Vec<String> = args
                    .iter()
                    .map(|a| self.ts_type(a, readonly, params, inputs))
                    .collect();
                format!("{name}<{}>", args.join(", "))
            }
            Boundary::Param(i) => params[*i].clone(),
        }
    }

    /// The declaration of data type `d`: its complete shape, which results
    /// have, or with `inputs` (when `d` is in it), its input shape
    /// `RangeOptionsInput`, which parameters have (§5.3, D1101). A field with
    /// a default is optional in the input shape: `step?: bigint`, or for an
    /// `Option`, `colour?: string | undefined`, since there `undefined` is
    /// `None` and a missing property the default (D1114). In the complete
    /// shape, a defaulted `Option` field is always present,
    /// `colour: string | undefined`. Other fields' types are input shapes
    /// too, all the way down.
    pub(crate) fn ts_alias(&self, d: DataId, inputs: Inputs) -> String {
        let data = self.g.data(d);
        let repr = repr(self.g, d);
        let params = self.ts_params(d);
        let mut name = type_name(data.name());
        if inputs.is_some() {
            name.push_str(INPUT_SUFFIX);
        }
        if repr.unboxed {
            // `js.unboxed`: a plain alias of its field's type (D1066). Its
            // fields are one with a key, and proofs.
            let field = self
                .generic_fields(d)
                .iter()
                .flatten()
                .next()
                .expect("an unboxed record has one field with a property");
            return format!(
                "export type {name} = {};\n",
                self.ts_type(&field.1, false, &params, inputs)
            );
        }
        let variants: Vec<String> = self
            .generic_fields(d)
            .iter()
            .enumerate()
            .map(|(c, fields)| {
                let mut parts = Vec::new();
                if !data.record() {
                    parts.push(format!(
                        "readonly {}: {}",
                        ts_key(&repr.tag_key),
                        js_string_literal(&repr.ctors[c].tag)
                    ));
                }
                for ((((_, b), key), flag), i) in fields
                    .iter()
                    .zip(external_keys(&repr, c))
                    .zip(external_optional(&repr, c))
                    .zip(runtime_fields(self.g, d, c))
                {
                    // A record's `Option` field is an optional property, and
                    // so is a variant's with `js.optional`; in an input, so
                    // is a field with a default.
                    let (optional, b) = if optional_property(self.g, d, c, i, b, flag) {
                        ("?", b.payload())
                    } else if inputs.is_some() && field_default(self.g, d, c, i).is_some() {
                        ("?", b.clone())
                    } else {
                        ("", b.clone())
                    };
                    // Lists in a declaration are mutable, `T[]`: an app's own
                    // types say `T[]`, and `readonly T[]` isn't assignable to
                    // it (see `ts_type`).
                    parts.push(format!(
                        "readonly {}{optional}: {}",
                        ts_key(key),
                        self.ts_type(&b, false, &params, inputs)
                    ));
                }
                if parts.is_empty() {
                    "{}".to_string()
                } else {
                    format!("{{ {} }}", parts.join("; "))
                }
            })
            .collect();
        let generics = if params.is_empty() {
            String::new()
        } else {
            format!("<{}>", params.join(", "))
        };
        if data.record() {
            // Structural, like every TypeScript object type: another record
            // with the same fields is accepted too (docs/proposals/records.md
            // §11.1).
            return format!("export type {name}{generics} = {};\n", variants[0]);
        }
        if repr.string_enum {
            // `js.enum`: each constructor is its string.
            let strings: Vec<String> = repr
                .ctors
                .iter()
                .map(|c| js_string_literal(&c.tag))
                .collect();
            return format!("export type {name}{generics} = {};\n", strings.join(" | "));
        }
        if variants.is_empty() {
            // A type without constructors has no values.
            return format!("export type {name}{generics} = never;\n");
        }
        format!(
            "export type {name}{generics} =\n  | {};\n",
            variants.join("\n  | ")
        )
    }

    /// TypeScript names for a data type's parameters: their own names where
    /// those can't be mistaken for anything else, otherwise `$0`, `$1`, …
    /// (Stitchwort names can't start with `$`.)
    pub(crate) fn ts_params(&self, d: DataId) -> Vec<String> {
        const TS_TYPE_WORDS: &[&str] = &[
            "any",
            "bigint",
            "boolean",
            "never",
            "null",
            "number",
            "object",
            "string",
            "symbol",
            "undefined",
            "unknown",
            "void",
        ];
        let data = self.g.data(d);
        data.params()
            .iter()
            .enumerate()
            .map(|(i, (x, _))| {
                let clear = is_js_identifier(x)
                    && !TS_TYPE_WORDS.contains(&&**x)
                    && !self
                        .g
                        .env
                        .datas()
                        .iter()
                        .any(|d| type_name(d.name()) == **x)
                    && data.params()[..i].iter().all(|(y, _)| y != x);
                if clear {
                    x.to_string()
                } else {
                    format!("${i}")
                }
            })
            .collect()
    }
}

/// Parameter names of a definition's leading lambdas.
pub(crate) fn lam_names(body: Option<&Term>) -> Vec<stitchwort_core::Name> {
    let mut names = Vec::new();
    let mut term = body.map(Term::strip_loc);
    while let Some(Term::Lam(x, _, inner, _)) = term {
        names.push(x.clone());
        term = Some(inner.strip_loc());
    }
    names
}

/// The type of parameter `i` as written in a signature (before evaluation).
pub(crate) fn written_param_type(ty: &Term, i: usize) -> Option<&Term> {
    let mut ty = ty.strip_loc();
    for _ in 0..i {
        let Term::Pi(_, _, _, cod, _) = ty else {
            return None;
        };
        ty = cod.strip_loc();
    }
    match ty {
        Term::Pi(_, _, dom, _, _) => Some(dom),
        _ => None,
    }
}

/// JS for a prelude definition with a native implementation (see
/// `stitchwort_core::native`). Like the evaluator's, these are trusted, and
/// tested against the definitions they replace.
pub(crate) fn native_js(op: native::Native) -> &'static str {
    use native::Native;
    match op {
        Native::Add => "(m) => (n) => m + n",
        Native::Sub => "(m) => (n) => (m >= n ? m - n : 0n)",
        Native::Mul => "(m) => (n) => m * n",
        Native::Leq => "(m) => (n) => ({ tag: m <= n ? \"True\" : \"False\" })",
        Native::EqNat => "(m) => (n) => ({ tag: m === n ? \"True\" : \"False\" })",
        Native::DivFuel => {
            "(fuel) => (n) => (d) => { if (d === 0n) return 0n; const q = n / d; return q < fuel ? q : fuel; }"
        }
    }
}

/// The one module that reinterprets a `Float`'s bits (docs/proposals/float.md
/// §3.5, D701): the only place a typed array or a `DataView` appears in
/// generated code (a test checks). A `Float` is a `number`, and a NaN may
/// have any payload in JS; these see every NaN as the one NaN.
/// `toCanonicalBits(fromCanonicalBits(b)) === b` for every valid canonical
/// `b`, and `Object.is(fromCanonicalBits(toCanonicalBits(x)), x)` for every
/// `number` `x`.
pub const FLOAT_BITS: &str = r#"// `Float` bit reinterpretation: a double's 64 bits, any NaN as the one NaN.
const floatView = new DataView(new ArrayBuffer(8));
const toCanonicalBits = (x) => {
  if (x !== x) return 0x7ff8000000000000n;
  floatView.setFloat64(0, x);
  return floatView.getBigUint64(0);
};
const fromCanonicalBits = (b) => {
  floatView.setBigUint64(0, b);
  return floatView.getFloat64(0);
};
"#;

/// The runtime's `FLOAT` codec (docs/proposals/float.md §5, D685): a `Float`
/// is a `number` inside generated code and at the boundary. Decoding accepts
/// every `number`, `NaN`, the infinities and `-0` included (finiteness
/// belongs on the application's own types, D702), and refuses anything else;
/// encoding passes the number on.
pub(crate) const FLOAT_CODEC: &str = "\n// `Float` is a `number`, any number, inside generated code too.\n\
const FLOAT = leaf((x) => (typeof x === \"number\" ? x : refuse(\"expected a number\")), (v) => v);\n";

/// JS for the double with valid `bits`: the shortest decimal that reads back
/// as it (Rust's `{:?}`, which a JS engine parses exactly, having at most 17
/// significant digits), `-0`, `NaN` or an infinity.
pub fn float_literal_js(bits: u64) -> String {
    let x = f64::from_bits(bits);
    if x.is_nan() {
        "NaN".into()
    } else if x.is_infinite() {
        if x > 0.0 { "Infinity" } else { "-Infinity" }.into()
    } else if x == 0.0 && x.is_sign_negative() {
        "-0".into()
    } else {
        let text = format!("{x:?}");
        if text.starts_with('-') {
            format!("({text})")
        } else {
            text
        }
    }
}

/// JS for a `Float` native: IEEE 754 doubles, as JS has them. `==` is
/// `Object.is` (the same double), JS's `===` is `Float.ieeeEq`; `<` is the
/// total order (`Float.compare`), JS's `<` is `Float.ieeeLt`. `native_int`
/// and `native_text` say whether an `Int` is a `bigint` and a `Text` a
/// string in generated code ([`Options`]); otherwise the conversions build
/// and read the constructors.
pub(crate) fn float_native_js(op: FloatPrim, native_int: bool, native_text: bool) -> String {
    let boolean = |test: &str| format!("({{ tag: {test} ? \"True\" : \"False\" }})");
    match op {
        FloatPrim::Add => "(a) => (b) => a + b".into(),
        FloatPrim::Sub => "(a) => (b) => a - b".into(),
        FloatPrim::Mul => "(a) => (b) => a * b".into(),
        FloatPrim::Div => "(a) => (b) => a / b".into(),
        FloatPrim::Rem => "(a) => (b) => a % b".into(),
        FloatPrim::Floor => "(a) => Math.floor(a)".into(),
        FloatPrim::Ceil => "(a) => Math.ceil(a)".into(),
        FloatPrim::Trunc => "(a) => Math.trunc(a)".into(),
        FloatPrim::Round => "(a) => Math.round(a)".into(),
        FloatPrim::Sqrt => "(a) => Math.sqrt(a)".into(),
        FloatPrim::OfNat => "(n) => Number(n)".into(),
        FloatPrim::OfInt if native_int => "(n) => Number(n)".into(),
        FloatPrim::OfInt => "(n) => Number(n.tag === \"OfNat\" ? n.n : -n.n - 1n)".into(),
        FloatPrim::ToText if native_text => "(a) => String(a)".into(),
        FloatPrim::ToText => "(a) => ({ tag: \"MkText\", chars: charsOfText(String(a)) })".into(),
        FloatPrim::Neg => "(a) => -a".into(),
        FloatPrim::Abs => "(a) => Math.abs(a)".into(),
        FloatPrim::IsNaN => format!("(a) => {}", boolean("a !== a")),
        FloatPrim::IsFinite => format!("(a) => {}", boolean("Number.isFinite(a)")),
        FloatPrim::DecEq => format!("(a) => (b) => {}", boolean("Object.is(a, b)")),
        FloatPrim::IeeeEq => format!("(a) => (b) => {}", boolean("a === b")),
        FloatPrim::IeeeLt => format!("(a) => (b) => {}", boolean("a < b")),
        FloatPrim::IeeeLe => format!("(a) => (b) => {}", boolean("a <= b")),
        // `BigInt` of a whole number is exact (and `BigInt(-0)` is `0n`).
        FloatPrim::ToInt if native_int => {
            "(a) => (Number.isInteger(a) ? { tag: \"Some\", value: BigInt(a) } : { tag: \"None\" })"
                .into()
        }
        FloatPrim::ToInt => "(a) => {\n  if (!Number.isInteger(a)) return { tag: \"None\" };\n  \
             const n = BigInt(a);\n  \
             return { tag: \"Some\", value: n >= 0n ? { tag: \"OfNat\", n } : { tag: \"NegSucc\", n: -n - 1n } };\n}"
            .into(),
        // IEEE 754's totalOrder, the NaN greatest: ordered numbers by `<`;
        // otherwise equal numbers, two zeros, or a NaN.
        FloatPrim::Compare => "(a) => (b) => ({\n  tag: a < b ? \"Less\" : a > b ? \"Greater\"\n    \
             : a !== a ? (b !== b ? \"Equal\" : \"Greater\") : b !== b ? \"Less\"\n    \
             : Object.is(a, b) ? \"Equal\" : Object.is(a, -0) ? \"Less\" : \"Greater\",\n})"
            .into(),
        // The same order's `<=` and `<`: JS's where it is ordered and the two
        // differ; otherwise (equal numbers, the zeros, or a NaN) the NaN is
        // greatest and equal to itself, and `-0` is below `0`.
        FloatPrim::Leq => format!(
            "(a) => (b) => {}",
            boolean(
                "(a < b || (a > b ? false : a !== a ? b !== b : b !== b || \
                 !Object.is(a, 0) || Object.is(b, 0)))"
            )
        ),
        FloatPrim::Less => format!(
            "(a) => (b) => {}",
            boolean(
                "(a < b || (a > b ? false : a !== a ? false : b !== b || \
                 (Object.is(a, -0) && Object.is(b, 0))))"
            )
        ),
        FloatPrim::FromBits => "fromCanonicalBits".into(),
        FloatPrim::Bits => "toCanonicalBits".into(),
    }
}

/// JS for an integer native. The prelude's types have the representation the
/// runtime uses (`Some`'s `value`, the constructors' names as tags). BigInt's
/// `/` and `%` truncate towards zero, and `%` takes the dividend's sign
/// (truncated division); the Euclidean and floored conventions correct that
/// by one step where the remainder has the wrong sign (Leijen, "Division and
/// modulus for computer scientists"). BigInt throws on a zero divisor, where
/// the prelude's divisions give 0 and leave the dividend as the remainder, so
/// each tests for it first.
pub(crate) fn int_native_js(op: IntNative) -> &'static str {
    match op {
        IntNative::NatToInt => "(n) => n",
        IntNative::IntNeg => "(a) => -a",
        IntNative::IntAdd => "(a) => (b) => a + b",
        IntNative::IntSub => "(a) => (b) => a - b",
        IntNative::IntMul => "(a) => (b) => a * b",
        // Euclidean: the remainder is never negative.
        IntNative::IntDiv => {
            "(a) => (d) => { if (d === 0n) return 0n; const q = a / d, r = a % d; return r < 0n ? (d > 0n ? q - 1n : q + 1n) : q; }"
        }
        IntNative::IntMod => {
            "(a) => (d) => { if (d === 0n) return a; const r = a % d; return r < 0n ? (d > 0n ? r + d : r - d) : r; }"
        }
        IntNative::IntTDiv => "(a) => (d) => (d === 0n ? 0n : a / d)",
        IntNative::IntTMod => "(a) => (d) => (d === 0n ? a : a % d)",
        // Floored: the remainder has the divisor's sign.
        IntNative::IntFDiv => {
            "(a) => (d) => { if (d === 0n) return 0n; const q = a / d, r = a % d; return r !== 0n && (r < 0n) !== (d < 0n) ? q - 1n : q; }"
        }
        IntNative::IntFMod => {
            "(a) => (d) => { if (d === 0n) return a; const r = a % d; return r !== 0n && (r < 0n) !== (d < 0n) ? r + d : r; }"
        }
        // The divisor is a `Nat`; by 0 it's `(a % 0).toNat`.
        IntNative::IntModNat => {
            "(a) => (d) => { if (d === 0n) return a < 0n ? 0n : a; const r = a % d; return r < 0n ? r + d : r; }"
        }
        IntNative::DecEqInt => "(a) => (b) => ({ tag: a === b ? \"True\" : \"False\" })",
        IntNative::IntLeq => "(a) => (b) => ({ tag: a <= b ? \"True\" : \"False\" })",
        IntNative::IntLess => "(a) => (b) => ({ tag: a < b ? \"True\" : \"False\" })",
        IntNative::IntCompare => {
            "(a) => (b) => ({ tag: a < b ? \"Less\" : a === b ? \"Equal\" : \"Greater\" })"
        }
        IntNative::IntNatAbs | IntNative::IntAbs => "(a) => (a < 0n ? -a : a)",
        IntNative::IntToNat => "(a) => (a < 0n ? 0n : a)",
        IntNative::IntToNatChecked => {
            "(a) => (a < 0n ? { tag: \"None\" } : { tag: \"Some\", value: a })"
        }
        IntNative::IntSign => "(a) => (a > 0n ? 1n : a < 0n ? -1n : 0n)",
        IntNative::IntToText => "(a) => a.toString()",
        // An optional `-`, then what `Text.toNat` accepts: one or more ASCII
        // digits and nothing else. (`BigInt` alone would also accept "",
        // " 12", "+5" and "0x10".) `-0` is `0`.
        IntNative::TextToInt => {
            r#"(t) => {
  const s = t.charCodeAt(0) === 45 ? t.slice(1) : t;
  if (s === "") return { tag: "None" };
  for (let i = 0; i < s.length; i++) {
    const unit = s.charCodeAt(i);
    if (unit < 48 || unit > 57) return { tag: "None" };
  }
  const n = BigInt(s);
  return { tag: "Some", value: s === t ? n : -n };
}"#
        }
    }
}

/// JS for an array native, on [`VERSION_ARRAYS`]'s helpers, which are in
/// scope. Each computes what the definition it replaces computes on the
/// array's list (`stitchwort_rt::natives::ArrayNative`).
pub(crate) fn array_native_js(op: ArrayNative) -> &'static str {
    match op {
        ArrayNative::FromList => "arrayOfList",
        ArrayNative::ToList => "listOfArray",
        ArrayNative::Size => "(a) => BigInt(arrayItems(a).length)",
        ArrayNative::Get => "(a) => (i) => arrayGet(a, i)",
        ArrayNative::GetOr => "(a) => (i) => (fallback) => arrayGetOr(a, i, fallback)",
        // The erased proof says the index is in range.
        ArrayNative::GetLt => "(a) => (i) => arrayItems(a)[Number(i)]",
        ArrayNative::Set => "(a) => (i) => (v) => arraySet(a, i, v)",
        ArrayNative::Push => "(a) => (v) => arrayPush(a, v)",
        ArrayNative::Pop => "arrayPop",
        ArrayNative::Replicate => {
            "(count) => (x) => arrayOfItems(new Array(Number(count)).fill(x))"
        }
    }
}

/// JS for a text native. The runtime's helpers (`TEXT_AS_STRING`) are in
/// scope, and the prelude's types have the representation the runtime uses
/// (`MkChar`'s `code`, `Cons`'s `head` and `tail`, `Some`'s `value`,
/// `MkPair`'s `fst` and `snd`).
pub(crate) fn text_native_js(op: TextNative) -> &'static str {
    match op {
        TextNative::TextGet
        | TextNative::TextGetOr
        | TextNative::TextGetLt
        | TextNative::TextSlice
        | TextNative::TextConcat => {
            unreachable!("internal error: {op:?} has no JS (`TextNative::in_js`)")
        }
        TextNative::TextToList => "charsOfText",
        TextNative::TextFromList => "textOfChars",
        TextNative::TextAppend => "(a) => (b) => a + b",
        // A surrogate pair is one character.
        TextNative::TextLength => {
            r#"(t) => {
  let n = 0;
  for (let i = 0; i < t.length; i++, n++) {
    const unit = t.charCodeAt(i);
    if (unit >= 0xd800 && unit <= 0xdbff) i++;
  }
  return BigInt(n);
}"#
        }
        TextNative::TextIsEmpty => r#"(t) => ({ tag: t === "" ? "True" : "False" })"#,
        // Well-formed UTF-16 is one-to-one with sequences of scalar values.
        TextNative::DecEqText => r#"(a) => (b) => ({ tag: a === b ? "True" : "False" })"#,
        // By scalar value, not code unit. At the first code unit that
        // differs, `codePointAt` gives each side's whole scalar value, or, if
        // the high halves of two pairs were the same, their low halves, which
        // are in the same order. A string that runs out first is a prefix,
        // ending between scalar values.
        TextNative::TextCompare => {
            r#"(a) => (b) => {
  const n = Math.min(a.length, b.length);
  for (let i = 0; i < n; i++) {
    if (a.charCodeAt(i) !== b.charCodeAt(i)) {
      return { tag: a.codePointAt(i) < b.codePointAt(i) ? "Less" : "Greater" };
    }
  }
  return { tag: a.length === b.length ? "Equal" : a.length < b.length ? "Less" : "Greater" };
}"#
        }
        TextNative::TextUncons => {
            r#"(t) => {
  if (t === "") return { tag: "None" };
  const code = t.codePointAt(0);
  const c = { tag: "MkChar", code: BigInt(code) };
  return { tag: "Some", value: { tag: "MkPair", fst: c, snd: t.slice(code > 0xffff ? 2 : 1) } };
}"#
        }
        // A right fold, as the definition is: `f` gets the last character
        // first. (The definition is strict and pure, so only the result can
        // differ, and it doesn't.) `f` itself may still recurse.
        TextNative::TextFold => {
            r#"(t) => (z) => (f) => {
  let acc = z;
  for (let i = t.length - 1; i >= 0; i--) {
    const code = scalarEndingAt(t, i);
    if (code > 0xffff) i--;
    acc = f({ tag: "MkChar", code: BigInt(code) })(acc);
  }
  return acc;
}"#
        }
        // Unicode `White_Space` (as `Char.isWhitespace`): U+0009..U+000D, U+0020,
        // U+0085, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F,
        // U+205F, U+3000. Not JS's `trim`, which adds U+FEFF and omits U+0085.
        TextNative::TextTrim => {
            r#"(t) => {
  const space = (u) =>
    (u >= 9 && u <= 13) || u === 32 || u === 0x85 || u === 0xa0 || u === 0x1680 ||
    (u >= 0x2000 && u <= 0x200a) || u === 0x2028 || u === 0x2029 || u === 0x202f ||
    u === 0x205f || u === 0x3000;
  let start = 0;
  let end = t.length;
  while (start < end && space(t.charCodeAt(start))) start++;
  while (end > start && space(t.charCodeAt(end - 1))) end--;
  return t.slice(start, end);
}"#
        }
        // The text `n` times over. Repeating whole strings keeps the pairs
        // of a well-formed string together.
        TextNative::TextRepeat => r#"(t) => (n) => t === "" ? "" : t.repeat(Number(n))"#,
        // The first `n` scalar values, or the whole text: a text has at most
        // as many scalar values as code units, so a count that reaches its
        // `length` takes it all without counting, and any other count is a
        // safe integer.
        TextNative::TextTake => {
            r#"(t) => (n) => {
  if (n >= BigInt(t.length)) return t;
  const count = Number(n);
  let i = 0;
  for (let k = 0; k < count && i < t.length; k++) {
    const unit = t.charCodeAt(i);
    i += unit >= 0xd800 && unit <= 0xdbff ? 2 : 1;
  }
  return t.slice(0, i);
}"#
        }
        // The text after its first `n` scalar values, or "".
        TextNative::TextDrop => {
            r#"(t) => (n) => {
  if (n >= BigInt(t.length)) return "";
  const count = Number(n);
  let i = 0;
  for (let k = 0; k < count && i < t.length; k++) {
    const unit = t.charCodeAt(i);
    i += unit >= 0xd800 && unit <= 0xdbff ? 2 : 1;
  }
  return t.slice(i);
}"#
        }
        // In well-formed strings a match of the needle's code units starts
        // with a whole scalar value (never a low surrogate) and ends with
        // one, so it is a match of scalar values. "" occurs in every text.
        TextNative::TextContains => {
            r#"(t) => (needle) => ({ tag: t.includes(needle) ? "True" : "False" })"#
        }
        // The separator is a whole scalar value, and in a well-formed string
        // a match can't start inside a pair. Empty fields are kept, and ""
        // splits into [""], as the definition says.
        TextNative::TextSplit => "(t) => (s) => listOf(t.split(encodeChar(s)))",
        TextNative::TextJoin => {
            r#"(ts) => (s) => {
  const parts = [];
  for (let l = ts; l.tag === "Cons"; l = l.tail) parts.push(l.head);
  return parts.join(encodeChar(s));
}"#
        }
        // Decimal, without leading zeros.
        TextNative::NatToText => "(n) => n.toString()",
        // One or more ASCII digits and nothing else; leading zeros are fine.
        // (`BigInt` alone would also accept "", " 12" and "0x10".)
        TextNative::TextToNat => {
            r#"(t) => {
  if (t === "") return { tag: "None" };
  for (let i = 0; i < t.length; i++) {
    const unit = t.charCodeAt(i);
    if (unit < 48 || unit > 57) return { tag: "None" };
  }
  return { tag: "Some", value: BigInt(t) };
}"#
        }
    }
}

/// Whether generated JS mentions the name, as a whole identifier.
pub(crate) fn mentions(js: &str, name: &str) -> bool {
    let part = |c: char| c.is_ascii_alphanumeric() || c == '_' || c == '$';
    js.match_indices(name).any(|(i, _)| {
        !js[..i].chars().next_back().is_some_and(part)
            && !js[i + name.len()..].chars().next().is_some_and(part)
    })
}

/// Whether variable 0 of `body` (the body of a `let`) is used at most once,
/// not inside a lambda (which may run any number of times) and not as a
/// `match`'s scrutinee (which must be a variable), so that its value can
/// be put in its place without computing it more often. Types and
/// equations, which run as `undefined` (`Gen::expr`), don't count: a
/// decision's proposition (`holds {a = b} d`) mentions its operands;
/// nor do a definition's erased arguments, or a call that's erased.
pub(crate) fn single_use<'t>(codegen: &Gen, body: &'t Term) -> bool {
    let mut uses = 0;
    let mut pending: Vec<(&'t Term, usize, bool)> = vec![(body, 0, false)];
    while let Some((term, binders, in_lambda)) = pending.pop() {
        let mut visit = |child: &'t Term, under: usize, lambda: bool| {
            pending.push((child, binders + under, in_lambda || lambda));
        };
        match term {
            Term::Var(ix) if *ix == binders => {
                uses += 1;
                if in_lambda || uses > 1 {
                    return false;
                }
            }
            Term::Case(ix, ..) | Term::NumCase(ix, ..) if *ix == binders => return false,
            Term::Data(..)
            | Term::Sort(_)
            | Term::Pi(..)
            | Term::Eq(..)
            | Term::Refl
            | Term::Quot(QuotForm::Type, ..) => {}
            Term::J(_, base, _, _) => visit(base, 0, false),
            Term::Let(_, _, value, body, _, _) => {
                visit(value, 0, false);
                visit(body, 1, false);
            }
            Term::Ann(inner, _) => visit(inner, 0, false),
            Term::Lam(_, _, inner, _) => visit(inner, 1, true),
            Term::App(..) => {
                let (head, args) = term.spine();
                let info = match head {
                    Term::Def(id) => codegen.try_info(*id).ok(),
                    _ => None,
                };
                match info {
                    Some(info) if info.result_erased => {}
                    _ => {
                        visit(head, 0, false);
                        for (i, arg) in args.into_iter().enumerate() {
                            if !info.is_some_and(|info| info.mask.get(i) == Some(&true)) {
                                visit(arg, 0, false);
                            }
                        }
                    }
                }
            }
            _ => term.for_each_child(|child, under| visit(child, under, false)),
        }
    }
    true
}

/// Whether variable 0 of `body` is a `match`'s scrutinee.
pub(crate) fn scrutinised(body: &Term) -> bool {
    body.subterms().any(|(term, binders)| {
        matches!(term, Term::Case(ix, ..) | Term::NumCase(ix, ..) if *ix == binders)
    })
}

pub(crate) fn var(level: usize) -> String {
    format!("v{level}")
}

/// How many of a definition's parameters, by erasure `mask`, are passed at
/// run time.
/// The function `rhs` calls, if `rhs` (a definition's generated right-hand
/// side) only passes its parameters on to it, in order: `(v0, v1) =>
/// g(v0, v1)`, or the same with `const`s renaming the parameters first
/// (a match on an unboxed record's one field is such a `const`):
///
/// ```js
/// (v0, v1) => {
///   const v2 = v0;
///   const v3 = v1;
///   return g(v2, v3);
/// }
/// ```
pub(crate) fn forwards_to(rhs: &str) -> Option<&str> {
    let (params, body) = rhs.split_once(" => ")?;
    let params: Vec<&str> = params
        .strip_prefix('(')?
        .strip_suffix(')')?
        .split(", ")
        .collect();
    if !params.iter().all(|p| is_js_identifier(p)) {
        return None;
    }
    // Each name in scope, with the parameter it is.
    let mut names: HashMap<&str, &str> = params.iter().map(|p| (*p, *p)).collect();
    let call = match body.strip_prefix("{\n").and_then(|b| b.strip_suffix('}')) {
        Some(block) => {
            let mut lines = block.lines().map(str::trim);
            loop {
                let line = lines.next()?;
                if let Some(binding) = line.strip_prefix("const ") {
                    let (x, value) = binding.strip_suffix(';')?.split_once(" = ")?;
                    let param = *names.get(value)?;
                    names.insert(x, param);
                } else {
                    let call = line.strip_prefix("return ")?.strip_suffix(';')?;
                    if lines.any(|l| !l.is_empty()) {
                        return None;
                    }
                    break call;
                }
            }
        }
        None => body,
    };
    let (head, args) = call.split_once('(')?;
    let args: Vec<&str> = args.strip_suffix(')')?.split(", ").collect();
    let passed: Option<Vec<&str>> = args.iter().map(|a| names.get(a).copied()).collect();
    (is_js_identifier(head) && !names.contains_key(head) && passed? == params).then_some(head)
}

pub(crate) fn runtime_params(mask: &[bool]) -> usize {
    mask.iter().filter(|erased| !**erased).count()
}

/// Whether the JS of an argument is a variable or a number literal, which
/// costs nothing to compute again, so a closure can mention it rather than
/// a copy computed outside.
pub(crate) fn is_simple(value: &str) -> bool {
    let value = value.strip_suffix('n').unwrap_or(value);
    let value = value.strip_prefix('v').unwrap_or(value);
    !value.is_empty() && value.chars().all(|c| c.is_ascii_digit())
}

/// `out`, a closure, with the names `bound` bound to their values, which
/// are computed once, before it's made: `(($s0) => out)(value)`.
pub(crate) fn bind_supplied<N: std::fmt::Display>(out: String, bound: Vec<(N, String)>) -> String {
    if bound.is_empty() {
        return out;
    }
    let (names, values): (Vec<String>, Vec<String>) = bound
        .into_iter()
        .map(|(name, value)| (name.to_string(), value))
        .unzip();
    format!("(({}) => {out})({})", names.join(", "), values.join(", "))
}

/// A native's JS that takes `k` arguments one at a time, `(a) => (b) =>
/// body`, as one function of all of them, `(a, b) => body` (D1173), if it
/// starts with `k` such parameters.
pub(crate) fn uncurry_arrows(js: &str, k: usize) -> Option<String> {
    let mut rest = js;
    let mut params = Vec::new();
    for _ in 0..k {
        let inner = rest.strip_prefix('(')?;
        let close = inner.find(')')?;
        let param = &inner[..close];
        if !is_js_identifier(param) {
            return None;
        }
        rest = inner[close + 1..].strip_prefix(" => ")?;
        params.push(param);
    }
    Some(format!("({}) => {rest}", params.join(", ")))
}

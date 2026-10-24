//! Inputs for counterexample search (docs/proposals/counterexample-search.md
//! §5): for each type, a [`Plan`] says how its values are made, and the
//! [`Inputs`] built from the plans enumerates them smallest first (§5.1
//! phase 1), draws random ones of a growing size (phase 2), and shrinks a
//! random counterexample (§5.5).
//!
//! Every value is a closed term made of constructors and numbers, except a
//! `Fin n` (`Fin.ofNatLt n i rfl`) and a `Map` (`Map.fromList xs`), which are
//! built by the library's own functions, so a map's invariant holds by
//! construction (§5.3). A proof field (`(ok: lo <= hi)`, a `Char`'s
//! `valid`) is `rfl`, and only when its proposition computes, at the fields
//! made, to an equation whose sides are the same (or a conjunction of
//! such): a value whose proof field doesn't hold is never made (§5.4).

use std::cell::RefCell;
use std::rc::Rc;

use stitchwort_core::collections::HashMap;
use stitchwort_core::registry::Builtin;
use stitchwort_core::value::{conv, eval, force, quote};
use stitchwort_core::{BigUint, DataId, DefId, Globals, Icit, Sort, Term, Value};

/// The largest total input size enumerated.
const MAX_SIZE: usize = 100;

/// The most data types one search makes inputs for.
const MAX_PLANS: usize = 64;

/// The largest `Vec` length enumerated (a `Vec a n` with a known `n`).
const MAX_VEC: usize = 64;

/// How deep a random value of a recursive type may nest.
const MAX_DEPTH: usize = 40;

/// How many times a random value with a proof field is drawn again when its
/// proof field doesn't hold.
const PROOF_RETRIES: usize = 16;

/// The characters enumerated, in order: a `Char`'s size is its position.
const ALPHABET: [char; 4] = ['a', 'b', '0', ' '];

/// The `Float`s enumerated, by size: `0.0`, then `1.0` and `-1.0`, then
/// halves and twos.
const FLOAT_TIERS: [&[f64]; 3] = [&[0.0], &[1.0, -1.0], &[0.5, 2.0, -0.5, -2.0]];

/// The `Float`s a random one is often drawn from: signed zero, the NaN,
/// the infinities, the extremes.
const FLOAT_EDGES: [f64; 8] = [
    -0.0,
    f64::NAN,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::MAX,
    f64::MIN_POSITIVE,
    0.1,
    1e300,
];

/// The values of one type of one size.
type Tier = Rc<Vec<Term>>;

/// One field of a constructor.
#[derive(Clone)]
enum Field {
    /// Data, made by a plan.
    Data(usize),
    /// A proof, of this type (in the context of the data type's parameters
    /// and the fields before it).
    Proof(Term),
}

/// How the values of one type are made.
enum Plan {
    /// Being worked out (a recursive type refers to itself).
    Pending,
    /// No inputs: some part of it has none.
    Failed,
    Nat,
    Int {
        int: DataId,
    },
    /// A `Char`: the alphabet, enumerated; any scalar value at random.
    Char {
        char_: DataId,
    },
    /// A `Float`, by its bits.
    Float {
        float: DataId,
    },
    /// `Fin n` for a known `n`: `Fin.ofNatLt n i rfl`.
    Fin {
        of_nat_lt: DefId,
        n: BigUint,
    },
    /// `Vec a n` for a known `n`: `n` elements, by its constructors.
    Vec {
        vec: DataId,
        elem: usize,
        n: usize,
        /// Where `VCons`'s length, head and tail are among its fields.
        layout: [usize; 3],
        /// `Vec.fromList`, which shows a vector.
        from_list: Option<DefId>,
    },
    /// `Map k v`: `head` (`Map.fromList` at its type and ordering) applied
    /// to a list of pairs, made by plan `list`.
    Map {
        head: Term,
        list: usize,
    },
    /// A data type or record: for each constructor, its fields. A `List`
    /// also has its element's plan, so a random one is drawn by length.
    Data {
        data: DataId,
        args: Vec<Value>,
        ctors: Vec<Vec<Field>>,
        list: Option<usize>,
    },
}

/// A random number generator: SplitMix64, seeded from the statement, so a
/// search is repeatable (§5.1).
pub struct Rng(u64);

impl Rng {
    pub fn new(seed: u64) -> Rng {
        Rng(seed)
    }

    /// The seed for a statement: a hash of its text.
    pub fn seed_of(text: &str) -> u64 {
        // FNV-1a.
        text.bytes().fold(0xcbf2_9ce4_8422_2325, |h, b| {
            (h ^ u64::from(b)).wrapping_mul(0x0100_0000_01b3)
        })
    }

    pub fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }

    /// A number from 0 to `n` inclusive.
    pub fn upto(&mut self, n: usize) -> usize {
        (self.next() % (n as u64 + 1)) as usize
    }

    /// True one time in `n`.
    fn one_in(&mut self, n: u64) -> bool {
        self.next().is_multiple_of(n)
    }
}

fn number(n: impl Into<BigUint>) -> Term {
    Term::Nat(Rc::new(n.into()))
}

/// A closed term's number, if it is one.
fn nat_of(term: &Term) -> Option<&BigUint> {
    match term.strip_loc() {
        Term::Nat(n) => Some(n),
        _ => None,
    }
}

/// Makes the inputs of the types it's given plans for.
pub struct Inputs<'g> {
    g: &'g Globals,
    plans: Vec<Plan>,
    keys: HashMap<String, usize>,
    tiers: RefCell<HashMap<(usize, usize), Tier>>,
    /// The most values of one type and size enumerated.
    tier_cap: usize,
}

impl<'g> Inputs<'g> {
    pub fn new(g: &'g Globals, tier_cap: usize) -> Self {
        Inputs {
            g,
            plans: Vec::new(),
            keys: HashMap::default(),
            tiers: RefCell::new(HashMap::default()),
            tier_cap,
        }
    }

    /// The plan for closed type `ty`, if it has inputs.
    pub fn plan(&mut self, ty: &Value) -> Option<usize> {
        let g = self.g;
        let ty = force(g, ty.clone()).ok()?;
        let Value::Data(d, args) = &ty else {
            return None;
        };
        let key = stitchwort_core::pretty::term(g, &[], &quote(g, 0, &ty).ok()?);
        if let Some(&plan) = self.keys.get(&key) {
            return match self.plans[plan] {
                Plan::Failed => None,
                _ => Some(plan),
            };
        }
        if self.plans.len() >= MAX_PLANS {
            return None;
        }
        let at = self.plans.len();
        self.keys.insert(key, at);
        let core = |b: Builtin| g.registry.is_data(b, *d);
        let library = |b: Builtin| g.registry.loaded_data(b) == Some(*d);
        if core(Builtin::Nat) {
            self.plans.push(Plan::Nat);
            return Some(at);
        }
        self.plans.push(Plan::Pending);
        let plan = if core(Builtin::Int) {
            Some(Plan::Int { int: *d })
        } else if core(Builtin::Char) {
            Some(Plan::Char { char_: *d })
        } else if library(Builtin::Float) {
            Some(Plan::Float { float: *d })
        } else if library(Builtin::Fin) {
            self.fin_plan(args)
        } else if library(Builtin::Map) {
            self.map_plan(*d, args)
        } else if g.data(*d).path.to_string() == "Std.Vec" {
            self.vec_plan(*d, args)
        } else {
            self.data_plan(*d, args)
        };
        match plan {
            Some(plan) => {
                self.plans[at] = plan;
                Some(at)
            }
            None => {
                self.plans[at] = Plan::Failed;
                None
            }
        }
    }

    /// `Fin n`, `n` a number.
    fn fin_plan(&mut self, args: &[Value]) -> Option<Plan> {
        let g = self.g;
        let [n] = args else { return None };
        let Value::Nat(n) = force(g, n.clone()).ok()? else {
            return None;
        };
        let of_nat_lt = g.registry.loaded_def(Builtin::FinOfNatLt)?;
        Some(Plan::Fin {
            of_nat_lt,
            n: (*n).clone(),
        })
    }

    /// `Vec a n`, `n` a number, if its constructors are `VNil` and `VCons`
    /// with a length, a head and a tail.
    fn vec_plan(&mut self, d: DataId, args: &[Value]) -> Option<Plan> {
        let g = self.g;
        let data = g.data(d);
        let [a, n] = args else { return None };
        let Value::Nat(n) = force(g, n.clone()).ok()? else {
            return None;
        };
        let n = usize::try_from(n.as_ref()).ok().filter(|n| *n <= MAX_VEC)?;
        let [nil, cons] = &data.ctors[..] else {
            return None;
        };
        if !nil.fields.is_empty() || cons.fields.len() != 3 {
            return None;
        }
        // The length is the field of type `Nat`; the tail the one of a type
        // of this data type; the head the other.
        let nat = g.registry.data(Builtin::Nat)?;
        let is = |t: &Term, f: &dyn Fn(&Term) -> bool| f(t.strip_loc());
        let length = cons.fields.iter().position(|(_, t)| {
            is(
                t,
                &|t| matches!(t, Term::Data(x, ps) if *x == nat && ps.is_empty()),
            )
        })?;
        let tail = cons
            .fields
            .iter()
            .position(|(_, t)| is(t, &|t| matches!(t, Term::Data(x, _) if *x == d)))?;
        let head = (0..3).find(|i| *i != length && *i != tail)?;
        let elem = self.plan(a)?;
        let from_list = g
            .defs
            .iter()
            .position(|def| def.path.to_string() == "Std.Vec.fromList")
            .map(DefId);
        Some(Plan::Vec {
            vec: d,
            elem,
            n,
            layout: [length, head, tail],
            from_list,
        })
    }

    /// `Map k v [ord]`: `Map.fromList` of a list of pairs.
    fn map_plan(&mut self, d: DataId, args: &[Value]) -> Option<Plan> {
        let g = self.g;
        let from_list = g.registry.loaded_def(Builtin::MapFromList)?;
        let list = g.registry.data(Builtin::List)?;
        let pair = g.registry.data(Builtin::Pair)?;
        let params = &g.data(d).params;
        if params.len() != args.len() {
            return None;
        }
        // `Map.fromList`'s implicit arguments, by name: the map's
        // parameters.
        let mut head = Term::Def(from_list);
        let mut ty = force(g, g.def(from_list).ty_value.clone()).ok()?;
        let mut explicit = 0;
        while let Value::Pi(x, icit, _, cod) = ty.clone() {
            if icit == Icit::Explicit {
                explicit += 1;
                break;
            }
            let at = params.iter().position(|(p, _)| *p == x)?;
            head = Term::app_icit(head, quote(g, 0, &args[at]).ok()?, icit);
            ty = force(g, cod.apply(g, args[at].clone()).ok()?).ok()?;
        }
        if explicit != 1 || args.len() < 2 {
            return None;
        }
        let pairs = Value::Data(
            list,
            vec![Value::Data(pair, vec![args[0].clone(), args[1].clone()])],
        );
        let list = self.plan(&pairs)?;
        Some(Plan::Map { head, list })
    }

    /// The plan for data type `d` applied to `args`.
    fn data_plan(&mut self, d: DataId, args: &[Value]) -> Option<Plan> {
        let g = self.g;
        let data = g.data(d);
        if !data.indices.is_empty() || data.sort == Sort::Prop || args.len() != data.params.len() {
            return None;
        }
        let mut ctors = Vec::new();
        for ctor in &data.ctors {
            let mut env: Vec<Value> = args.to_vec();
            let mut fields = Vec::new();
            for (j, ((_, field_ty), (erased, sort))) in ctor
                .fields
                .iter()
                .zip(ctor.field_erased.iter().zip(&ctor.field_sorts))
                .enumerate()
            {
                if *erased {
                    // A proof field: one whose proposition computes to
                    // equations (§5.4). A type field: none.
                    if *sort != Sort::Prop || !self.decidable(&env, field_ty) {
                        return None;
                    }
                    fields.push(Field::Proof(field_ty.clone()));
                } else {
                    // A field whose type depends on an earlier field.
                    if (0..j).any(|ix| field_ty.mentions(ix)) {
                        return None;
                    }
                    let field = eval(g, &env, field_ty).ok()?;
                    fields.push(Field::Data(self.plan(&field)?));
                }
                env.push(Value::var(args.len() + j));
            }
            ctors.push(fields);
        }
        let list = if g.registry.is_data(Builtin::List, d) {
            match ctors.get(1).map(Vec::as_slice) {
                Some([Field::Data(elem), Field::Data(_)]) => Some(*elem),
                _ => None,
            }
        } else {
            None
        };
        Some(Plan::Data {
            data: d,
            args: args.to_vec(),
            ctors,
            list,
        })
    }

    /// Whether proposition `prop` (in `env`, the fields as variables) is
    /// one [`Inputs::proof`] can decide once they're known: an equation,
    /// or a conjunction of them.
    fn decidable(&self, env: &[Value], prop: &Term) -> bool {
        let g = self.g;
        let Ok(value) = eval(g, env, prop).and_then(|v| force(g, v)) else {
            return false;
        };
        self.decidable_value(&value, 0)
    }

    fn decidable_value(&self, value: &Value, depth: usize) -> bool {
        let g = self.g;
        match value {
            Value::Eq(..) => true,
            Value::Data(d, args) if depth < 8 && g.registry.is_data(Builtin::And, *d) => args
                .iter()
                .all(|a| force(g, a.clone()).is_ok_and(|a| self.decidable_value(&a, depth + 1))),
            Value::Data(d, _) => g.registry.is_data(Builtin::Unit, *d),
            _ => false,
        }
    }

    /// A proof of `prop` (closed, a value), if it holds by computation: an
    /// equation whose sides are the same is `rfl`, a conjunction the pair of
    /// its proofs.
    fn proof(&self, prop: Value, depth: usize) -> Option<Term> {
        let g = self.g;
        let prop = force(g, prop).ok()?;
        match prop {
            Value::Eq(_, a, b) => conv(g, 0, &a, &b).ok()?.then_some(Term::Refl),
            Value::Data(d, args) if depth < 8 && g.registry.is_data(Builtin::And, d) => {
                let parts = args
                    .into_iter()
                    .map(|a| self.proof(a, depth + 1))
                    .collect::<Option<Vec<Term>>>()?;
                Some(Term::ctor(d, 0, parts))
            }
            Value::Data(d, _) if g.registry.is_data(Builtin::Unit, d) => {
                Some(Term::ctor(d, 0, Vec::new()))
            }
            _ => None,
        }
    }

    /// Constructor `c` of data plan `plan` with data fields `parts`, its
    /// proof fields made: `None` if one doesn't hold.
    fn build(&self, plan: usize, c: usize, parts: Vec<Term>) -> Option<Term> {
        let Plan::Data {
            data, args, ctors, ..
        } = &self.plans[plan]
        else {
            return None;
        };
        let fields = &ctors[c];
        if fields.iter().all(|f| matches!(f, Field::Data(_))) {
            return Some(Term::ctor(*data, c, parts));
        }
        let g = self.g;
        let mut env: Vec<Value> = args.clone();
        let mut out = Vec::with_capacity(fields.len());
        let mut parts = parts.into_iter();
        for field in fields {
            match field {
                Field::Data(_) => {
                    let part = parts.next()?;
                    env.push(eval(g, &[], &part).ok()?);
                    out.push(part);
                }
                Field::Proof(prop) => {
                    let proof = self.proof(eval(g, &env, prop).ok()?, 0)?;
                    env.push(stitchwort_core::erase::erased());
                    out.push(proof);
                }
            }
        }
        Some(Term::ctor(*data, c, out))
    }

    /// The data fields' plans of constructor `c` of data plan `plan`.
    fn data_fields(&self, plan: usize, c: usize) -> Vec<usize> {
        match &self.plans[plan] {
            Plan::Data { ctors, .. } => ctors[c]
                .iter()
                .filter_map(|f| match f {
                    Field::Data(p) => Some(*p),
                    Field::Proof(_) => None,
                })
                .collect(),
            _ => Vec::new(),
        }
    }

    // Enumeration (§5.1 phase 1).

    /// The values of plan `plan` of size `size`, at most the tier cap.
    fn tier(&self, plan: usize, size: usize) -> Tier {
        if let Some(tier) = self.tiers.borrow().get(&(plan, size)) {
            return tier.clone();
        }
        let cap = self.tier_cap;
        let values = match &self.plans[plan] {
            Plan::Pending | Plan::Failed => Vec::new(),
            Plan::Nat => vec![number(size)],
            // 0, 1, -1, 2, -2, …: `OfNat n` and `NegSucc (n - 1)`.
            Plan::Int { int } => {
                let mut values = vec![Term::ctor(*int, 0, vec![number(size)])];
                if size > 0 {
                    values.push(Term::ctor(*int, 1, vec![number(size - 1)]));
                }
                values
            }
            Plan::Char { char_ } => ALPHABET
                .get(size)
                .map(|c| vec![char_term(*char_, *c)])
                .unwrap_or_default(),
            Plan::Float { float } => FLOAT_TIERS
                .get(size)
                .map(|xs| xs.iter().map(|x| float_term(*float, *x)).collect())
                .unwrap_or_default(),
            Plan::Fin { of_nat_lt, n } => {
                if BigUint::from(size) < *n {
                    vec![fin_term(*of_nat_lt, n, BigUint::from(size))]
                } else {
                    Vec::new()
                }
            }
            Plan::Vec {
                vec,
                elem,
                n,
                layout,
                ..
            } => {
                let mut values = Vec::new();
                self.products(&vec![*elem; *n], size, cap, &mut |parts| {
                    values.push(vec_term(*vec, *layout, parts));
                    values.len() < cap
                });
                values
            }
            Plan::Map { head, list } => self
                .tier(*list, size)
                .iter()
                .map(|xs| Term::app(head.clone(), xs.clone()))
                .collect(),
            Plan::Data { ctors, .. } => {
                let mut values = Vec::new();
                for c in 0..ctors.len() {
                    let fields = self.data_fields(plan, c);
                    if fields.is_empty() {
                        if size == 0
                            && let Some(v) = self.build(plan, c, Vec::new())
                        {
                            values.push(v);
                        }
                    } else if size > 0 {
                        self.products(&fields, size - 1, cap, &mut |parts| {
                            if let Some(v) = self.build(plan, c, parts) {
                                values.push(v);
                            }
                            values.len() < cap
                        });
                    }
                    if values.len() >= cap {
                        break;
                    }
                }
                values
            }
        };
        let values = Rc::new(values);
        self.tiers.borrow_mut().insert((plan, size), values.clone());
        values
    }

    /// Calls `each` with every tuple of values of `plans` whose sizes add up
    /// to `total`, in order (the first plan's smallest first), until it says
    /// to stop or `limit` tuples have been made. Whether it stopped.
    fn products(
        &self,
        plans: &[usize],
        total: usize,
        limit: usize,
        each: &mut dyn FnMut(Vec<Term>) -> bool,
    ) -> bool {
        let mut made = 0;
        let mut sizes = vec![0; plans.len()];
        let mut stop = false;
        compositions(total, plans.len(), &mut sizes, 0, &mut |sizes| {
            let tiers: Vec<Tier> = plans
                .iter()
                .zip(sizes)
                .map(|(p, s)| self.tier(*p, *s))
                .collect();
            if tiers.iter().any(|t| t.is_empty()) {
                return true;
            }
            // Every combination, the last plan's value changing fastest.
            let mut at = vec![0; tiers.len()];
            loop {
                let tuple = at.iter().zip(&tiers).map(|(i, t)| t[*i].clone()).collect();
                made += 1;
                if !each(tuple) || made >= limit {
                    stop = true;
                    return false;
                }
                let mut k = tiers.len();
                loop {
                    if k == 0 {
                        return true;
                    }
                    k -= 1;
                    at[k] += 1;
                    if at[k] < tiers[k].len() {
                        break;
                    }
                    at[k] = 0;
                }
            }
        });
        stop
    }

    /// Up to `max` tuples of inputs for `plans`, smallest total size first;
    /// the largest total size reached; and whether they're all there are
    /// (finitely many: all `Bool`s, say).
    pub fn enumerate(&self, plans: &[usize], max: usize) -> (Vec<Vec<Term>>, usize, bool) {
        if plans.is_empty() {
            return (vec![Vec::new()], 0, true);
        }
        let mut out = Vec::new();
        let mut empty_sizes = 0;
        let mut largest = 0;
        for total in 0..=MAX_SIZE {
            let before = out.len();
            let stopped = self.products(plans, total, max - out.len(), &mut |tuple| {
                out.push(tuple);
                out.len() < max
            });
            if out.len() > before {
                largest = total;
            }
            if stopped || out.len() >= max {
                return (out, largest, false);
            }
            empty_sizes = if out.len() == before {
                empty_sizes + 1
            } else {
                0
            };
            if empty_sizes > 8 {
                let all = !plans.iter().any(|p| self.more_at_random(*p));
                return (out, largest, all);
            }
        }
        (out, largest, false)
    }

    // Random values (§5.1 phase 2).

    /// A random tuple of inputs for `plans`, each of size up to `size`.
    pub fn random_tuple(&self, plans: &[usize], size: usize, rng: &mut Rng) -> Option<Vec<Term>> {
        plans
            .iter()
            .map(|p| self.random(*p, size, rng, 0))
            .collect()
    }

    /// A random value of plan `plan` of size up to `size`: sometimes an edge
    /// value (a number past a machine word, a non-ASCII character, a NaN).
    fn random(&self, plan: usize, size: usize, rng: &mut Rng, depth: usize) -> Option<Term> {
        if depth > MAX_DEPTH {
            return None;
        }
        match &self.plans[plan] {
            Plan::Pending | Plan::Failed => None,
            Plan::Nat => Some(number(random_nat(size, rng))),
            Plan::Int { int } => {
                let magnitude = random_nat(size, rng);
                Some(if rng.one_in(2) || magnitude == BigUint::from(0u32) {
                    Term::ctor(*int, 0, vec![number(magnitude)])
                } else {
                    Term::ctor(*int, 1, vec![number(magnitude - 1u32)])
                })
            }
            Plan::Char { char_ } => Some(char_term(*char_, random_char(rng))),
            Plan::Float { float } => {
                let x = if rng.one_in(4) {
                    FLOAT_EDGES[rng.upto(FLOAT_EDGES.len() - 1)]
                } else {
                    let whole = rng.upto(2 * size) as f64 - size as f64;
                    whole / f64::from(1u32 << rng.upto(4))
                };
                Some(float_term(*float, x))
            }
            Plan::Fin { of_nat_lt, n } => {
                if *n == BigUint::from(0u32) {
                    return None;
                }
                let i = BigUint::from(rng.next()) % n;
                Some(fin_term(*of_nat_lt, n, i))
            }
            Plan::Vec {
                vec,
                elem,
                n,
                layout,
                ..
            } => {
                let parts = (0..*n)
                    .map(|_| self.random(*elem, size, rng, depth + 1))
                    .collect::<Option<Vec<Term>>>()?;
                Some(vec_term(*vec, *layout, parts))
            }
            Plan::Map { head, list } => Some(Term::app(
                head.clone(),
                self.random(*list, size, rng, depth + 1)?,
            )),
            Plan::Data {
                data, ctors, list, ..
            } => {
                // A list by its length, up to the size, as QuickCheck does.
                if let Some(elem) = list {
                    let length = rng.upto(size);
                    let items = (0..length)
                        .map(|_| self.random(*elem, size, rng, depth + 1))
                        .collect::<Option<Vec<Term>>>()?;
                    return Some(list_term(*data, items));
                }
                for _ in 0..PROOF_RETRIES {
                    // At size 0, a constructor without data fields where
                    // there is one.
                    let leaves: Vec<usize> = (0..ctors.len())
                        .filter(|c| self.data_fields(plan, *c).is_empty())
                        .collect();
                    let c = if size == 0 && !leaves.is_empty() {
                        leaves[rng.upto(leaves.len() - 1)]
                    } else {
                        rng.upto(ctors.len() - 1)
                    };
                    let fields = self.data_fields(plan, c);
                    // The size left, shared among the fields at random.
                    let weights: Vec<u64> = fields.iter().map(|_| rng.next() >> 40).collect();
                    let total: u64 = weights.iter().sum::<u64>().max(1);
                    let left = size.saturating_sub(1) as u64;
                    let parts = fields
                        .iter()
                        .zip(&weights)
                        .map(|(p, w)| {
                            let share = (left * w / total) as usize;
                            self.random(*p, share, rng, depth + 1)
                        })
                        .collect::<Option<Vec<Term>>>()?;
                    if let Some(value) = self.build(plan, c, parts) {
                        return Some(value);
                    }
                }
                None
            }
        }
    }

    // Shrinking (§5.5).

    /// Inputs like `input` but smaller in one place, the most promising
    /// first.
    pub fn shrink_tuple(&self, plans: &[usize], input: &[Term]) -> Vec<Vec<Term>> {
        let mut out = Vec::new();
        for (i, (plan, value)) in plans.iter().zip(input).enumerate() {
            for smaller in self.shrink(*plan, value) {
                let mut candidate = input.to_vec();
                candidate[i] = smaller;
                out.push(candidate);
            }
        }
        out
    }

    /// Values of plan `plan` smaller than `value`: subterms of the same
    /// type, numbers halved and decremented toward 0, list elements
    /// removed, and each part shrunk in place.
    fn shrink(&self, plan: usize, value: &Term) -> Vec<Term> {
        let value = value.strip_loc();
        match &self.plans[plan] {
            Plan::Pending | Plan::Failed => Vec::new(),
            Plan::Nat => nat_of(value)
                .map(shrink_nat)
                .unwrap_or_default()
                .into_iter()
                .map(number)
                .collect(),
            Plan::Int { int } => {
                let Term::Ctor(_, c, fields) = value else {
                    return Vec::new();
                };
                let Some(n) = fields.first().and_then(|f| nat_of(f)) else {
                    return Vec::new();
                };
                if *c == 0 {
                    shrink_nat(n)
                        .into_iter()
                        .map(|m| Term::ctor(*int, 0, vec![number(m)]))
                        .collect()
                } else {
                    // `-(n + 1)`: its negation first, then toward 0.
                    let mut out = vec![Term::ctor(*int, 0, vec![number(n + 1u32)])];
                    out.push(Term::ctor(*int, 0, vec![number(0u32)]));
                    out.extend(
                        shrink_nat(n)
                            .into_iter()
                            .map(|m| Term::ctor(*int, 1, vec![number(m)])),
                    );
                    out
                }
            }
            Plan::Char { char_ } => {
                let Some(code) = char_code(value) else {
                    return Vec::new();
                };
                // The alphabet's earlier characters; outside it, also
                // smaller codes, as numbers shrink.
                let at = ALPHABET.iter().position(|c| *c as u32 == code);
                let mut out: Vec<char> = ALPHABET[..at.unwrap_or(ALPHABET.len())].to_vec();
                if at.is_none() {
                    for smaller in shrink_nat(&BigUint::from(code)) {
                        if let Some(c) = u32::try_from(&smaller).ok().and_then(char::from_u32)
                            && !out.contains(&c)
                        {
                            out.push(c);
                        }
                    }
                }
                out.into_iter().map(|c| char_term(*char_, c)).collect()
            }
            Plan::Float { float } => {
                let Some(x) = float_of(value) else {
                    return Vec::new();
                };
                let mut out = Vec::new();
                for smaller in [0.0, 1.0, x.trunc(), x / 2.0] {
                    if smaller.to_bits() != x.to_bits()
                        && (smaller.abs() < x.abs() || !x.is_finite())
                        && !out.iter().any(|y: &f64| y.to_bits() == smaller.to_bits())
                    {
                        out.push(smaller);
                    }
                }
                out.into_iter().map(|y| float_term(*float, y)).collect()
            }
            Plan::Fin { of_nat_lt, n } => {
                let (_, args) = value.spine();
                let Some(i) = args.get(1).and_then(|a| nat_of(a)) else {
                    return Vec::new();
                };
                shrink_nat(i)
                    .into_iter()
                    .map(|j| fin_term(*of_nat_lt, n, j))
                    .collect()
            }
            Plan::Vec {
                vec, elem, layout, ..
            } => {
                let items = vec_items(value, *layout);
                let mut out = Vec::new();
                for (i, item) in items.iter().enumerate() {
                    for smaller in self.shrink(*elem, item) {
                        let mut parts = items.clone();
                        parts[i] = smaller;
                        out.push(vec_term(*vec, *layout, parts));
                    }
                }
                out
            }
            Plan::Map { head, list } => {
                let Term::App(_, xs, _) = value else {
                    return Vec::new();
                };
                self.shrink(*list, xs)
                    .into_iter()
                    .map(|ys| Term::app(head.clone(), ys))
                    .collect()
            }
            Plan::Data {
                data, list, ctors, ..
            } => {
                if let Some(elem) = list {
                    let Some(items) = list_items(value) else {
                        return Vec::new();
                    };
                    return shrink_list(&items, &|item| self.shrink(*elem, item))
                        .into_iter()
                        .map(|items| list_term(*data, items))
                        .collect();
                }
                let Term::Ctor(_, c, fields) = value else {
                    return Vec::new();
                };
                let Some(kinds) = ctors.get(*c) else {
                    return Vec::new();
                };
                let parts: Vec<(usize, Term)> = kinds
                    .iter()
                    .zip(fields)
                    .filter_map(|(k, f)| match k {
                        Field::Data(p) => Some((*p, (**f).clone())),
                        Field::Proof(_) => None,
                    })
                    .collect();
                let mut out = Vec::new();
                // A part of the same type.
                for (p, part) in &parts {
                    if *p == plan {
                        out.push(part.clone());
                    }
                }
                // Each part shrunk.
                for (i, (p, part)) in parts.iter().enumerate() {
                    for smaller in self.shrink(*p, part) {
                        let mut new: Vec<Term> = parts.iter().map(|(_, t)| t.clone()).collect();
                        new[i] = smaller;
                        if let Some(v) = self.build(plan, *c, new) {
                            out.push(v);
                        }
                    }
                }
                out
            }
        }
    }

    // Showing (§9.1).

    /// Input `value` of plan `plan` as it's shown: like the value, except a
    /// `Fin` is its number and a `Vec` is `Vec.fromList` of its elements.
    pub fn shown(&self, plan: usize, value: &Term) -> Term {
        match &self.plans[plan] {
            Plan::Fin { .. } => {
                let (_, args) = value.spine();
                args.get(1).map_or_else(|| value.clone(), |i| (*i).clone())
            }
            Plan::Vec {
                vec,
                elem,
                layout,
                from_list,
                ..
            } => {
                let items = vec_items(value, *layout)
                    .iter()
                    .map(|item| self.shown(*elem, item))
                    .collect();
                match (from_list, self.g.registry.data(Builtin::List)) {
                    (Some(from_list), Some(list)) => {
                        Term::app(Term::Def(*from_list), list_term(list, items))
                    }
                    _ => vec_term(*vec, *layout, items),
                }
            }
            Plan::Map { head, list } => match value.strip_loc() {
                Term::App(_, xs, _) => Term::app(head.clone(), self.shown(*list, xs)),
                _ => value.clone(),
            },
            Plan::Data { ctors, .. } => match value.strip_loc() {
                Term::Ctor(d, c, fields) => {
                    let Some(kinds) = ctors.get(*c) else {
                        return value.clone();
                    };
                    let fields = kinds
                        .iter()
                        .zip(fields)
                        .map(|(k, f)| match k {
                            Field::Data(p) => self.shown(*p, f),
                            Field::Proof(_) => (**f).clone(),
                        })
                        .collect();
                    Term::ctor(*d, *c, fields)
                }
                _ => value.clone(),
            },
            _ => value.clone(),
        }
    }

    /// Whether plan `plan`'s values are shown as terms rather than values
    /// (a `Map`, a `Fin`, a `Vec`, a proof field, or something containing
    /// one): the value of `Map.fromList xs` is its tree, and a proof is
    /// erased in a value.
    pub fn shown_as_term(&self, plan: usize) -> bool {
        self.reaches(plan, &|p| match p {
            Plan::Fin { .. } | Plan::Map { .. } | Plan::Vec { .. } => true,
            Plan::Data { ctors, .. } => {
                ctors.iter().flatten().any(|f| matches!(f, Field::Proof(_)))
            }
            _ => false,
        })
    }

    /// Whether random inputs of plan `plan` can be ones enumeration never
    /// makes, even when it makes all it can (a non-ASCII `Char`, a NaN).
    fn more_at_random(&self, plan: usize) -> bool {
        self.reaches(plan, &|p| {
            matches!(p, Plan::Char { .. } | Plan::Float { .. })
        })
    }

    /// Whether `test` holds for plan `plan` or one of its parts.
    fn reaches(&self, plan: usize, test: &dyn Fn(&Plan) -> bool) -> bool {
        let mut seen = Vec::new();
        let mut pending = vec![plan];
        while let Some(plan) = pending.pop() {
            if seen.contains(&plan) {
                continue;
            }
            seen.push(plan);
            let p = &self.plans[plan];
            if test(p) {
                return true;
            }
            match p {
                Plan::Vec { elem, .. } => pending.push(*elem),
                Plan::Map { list, .. } => pending.push(*list),
                Plan::Data { ctors, .. } => {
                    pending.extend(ctors.iter().flatten().filter_map(|f| match f {
                        Field::Data(p) => Some(*p),
                        Field::Proof(_) => None,
                    }));
                }
                _ => {}
            }
        }
        false
    }
}

/// A random number up to `size`, or, one time in ten, one at an edge of a
/// machine word (the fast runtime switches representation at 2^64,
/// `rt/src/value.rs`).
fn random_nat(size: usize, rng: &mut Rng) -> BigUint {
    if rng.one_in(10) {
        let two = BigUint::from(2u32);
        let edges = [
            two.pow(32),
            two.pow(63),
            two.pow(64) - 1u32,
            two.pow(64),
            two.pow(64) + 1u32,
        ];
        return edges[rng.upto(edges.len() - 1)].clone();
    }
    BigUint::from(rng.upto(size))
}

/// Numbers smaller than `n`, smallest first: 0, then `n` less a half, a
/// quarter, an eighth, … of it, down to one less (QuickCheck's
/// `shrinkIntegral`), so shrinking toward a boundary takes about log² n
/// steps, not n.
fn shrink_nat(n: &BigUint) -> Vec<BigUint> {
    let zero = BigUint::from(0u32);
    if *n == zero {
        return Vec::new();
    }
    let mut out = vec![zero];
    let mut part: BigUint = n >> 1;
    while part > BigUint::from(0u32) {
        let smaller = n - &part;
        if !out.contains(&smaller) {
            out.push(smaller);
        }
        part >>= 1;
    }
    let less = n - 1u32;
    if !out.contains(&less) {
        out.push(less);
    }
    out
}

/// A random character: mostly from the alphabet, sometimes any printable
/// ASCII one, sometimes any scalar value, including ones outside the
/// Basic Multilingual Plane.
fn random_char(rng: &mut Rng) -> char {
    match rng.upto(9) {
        0..=5 => ALPHABET[rng.upto(ALPHABET.len() - 1)],
        6 | 7 => char::from(b' ' + rng.upto(94) as u8),
        8 => ['é', 'ß', 'λ', '中', '😀'][rng.upto(4)],
        _ => loop {
            if let Some(c) = char::from_u32((rng.next() % 0x11_0000) as u32) {
                break c;
            }
        },
    }
}

/// Lists smaller than `items`: empty, either half, one element removed,
/// one element shrunk.
fn shrink_list(items: &[Term], shrink: &dyn Fn(&Term) -> Vec<Term>) -> Vec<Vec<Term>> {
    let n = items.len();
    let mut out: Vec<Vec<Term>> = Vec::new();
    if n == 0 {
        return out;
    }
    out.push(Vec::new());
    if n > 2 {
        out.push(items[n / 2..].to_vec());
        out.push(items[..n / 2].to_vec());
    }
    if n > 1 {
        for i in 0..n {
            let mut fewer = items.to_vec();
            fewer.remove(i);
            out.push(fewer);
        }
    }
    for (i, item) in items.iter().enumerate() {
        for smaller in shrink(item) {
            let mut new = items.to_vec();
            new[i] = smaller;
            out.push(new);
        }
    }
    out
}

fn char_term(char_: DataId, c: char) -> Term {
    Term::ctor(char_, 0, vec![number(c as u32), Term::Refl])
}

fn char_code(term: &Term) -> Option<u32> {
    match term.strip_loc() {
        Term::Ctor(_, 0, fields) => u32::try_from(nat_of(fields.first()?)?).ok(),
        _ => None,
    }
}

/// A `Float` from its double, with the NaN canonical (D701).
fn float_term(float: DataId, x: f64) -> Term {
    let bits = if x.is_nan() {
        0x7FF8_0000_0000_0000
    } else {
        x.to_bits()
    };
    Term::ctor(float, 0, vec![number(bits), Term::Refl])
}

fn float_of(term: &Term) -> Option<f64> {
    match term.strip_loc() {
        Term::Ctor(_, 0, fields) => Some(f64::from_bits(
            u64::try_from(nat_of(fields.first()?)?).ok()?,
        )),
        _ => None,
    }
}

fn fin_term(of_nat_lt: DefId, n: &BigUint, i: BigUint) -> Term {
    Term::app(
        Term::app(
            Term::app(Term::Def(of_nat_lt), number(n.clone())),
            number(i),
        ),
        Term::Refl,
    )
}

/// The vector of `items`, its constructors' fields laid out as `layout`
/// says (length, head, tail).
fn vec_term(vec: DataId, layout: [usize; 3], items: Vec<Term>) -> Term {
    let [length, head, tail] = layout;
    items
        .into_iter()
        .rev()
        .enumerate()
        .fold(Term::ctor(vec, 0, Vec::new()), |rest, (k, item)| {
            let mut fields = vec![Term::Refl, Term::Refl, Term::Refl];
            fields[length] = number(k);
            fields[head] = item;
            fields[tail] = rest;
            Term::ctor(vec, 1, fields)
        })
}

fn vec_items(term: &Term, layout: [usize; 3]) -> Vec<Term> {
    let [_, head, tail] = layout;
    let mut items = Vec::new();
    let mut at = term.strip_loc();
    while let Term::Ctor(_, 1, fields) = at {
        items.push((*fields[head]).clone());
        at = fields[tail].strip_loc();
    }
    items
}

fn list_term(list: DataId, items: Vec<Term>) -> Term {
    items
        .into_iter()
        .rev()
        .fold(Term::ctor(list, 0, Vec::new()), |rest, item| {
            Term::ctor(list, 1, vec![item, rest])
        })
}

fn list_items(term: &Term) -> Option<Vec<Term>> {
    let mut items = Vec::new();
    let mut at = term.strip_loc();
    loop {
        match at {
            Term::Ctor(_, 0, _) => return Some(items),
            Term::Ctor(_, 1, fields) if fields.len() == 2 => {
                items.push((*fields[0]).clone());
                at = fields[1].strip_loc();
            }
            _ => return None,
        }
    }
}

/// Calls `each` with every way of writing `total` as `parts` sizes, in
/// order, until it says to stop. Whether it was told to stop.
fn compositions(
    total: usize,
    parts: usize,
    sizes: &mut Vec<usize>,
    from: usize,
    each: &mut dyn FnMut(&[usize]) -> bool,
) -> bool {
    if from + 1 >= parts {
        if parts == 0 {
            return total != 0 || each(sizes);
        }
        sizes[from] = total;
        return each(sizes);
    }
    for size in 0..=total {
        sizes[from] = size;
        if !compositions(total - size, parts, sizes, from + 1, each) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::{BigUint, Rng, compositions, shrink_nat};

    fn all(total: usize, parts: usize) -> Vec<Vec<usize>> {
        let mut found = Vec::new();
        let mut sizes = vec![0; parts];
        compositions(total, parts, &mut sizes, 0, &mut |s| {
            found.push(s.to_vec());
            true
        });
        found
    }

    #[test]
    fn sizes_are_split_every_way_the_first_smallest_first() {
        assert_eq!(all(2, 2), [[0, 2], [1, 1], [2, 0]]);
        assert_eq!(all(1, 3), [[0, 0, 1], [0, 1, 0], [1, 0, 0]]);
        assert_eq!(all(3, 1), [[3]]);
        assert_eq!(all(0, 2), [[0, 0]]);
    }

    #[test]
    fn splitting_stops_when_told() {
        let mut seen = 0;
        let mut sizes = vec![0; 2];
        let finished = compositions(5, 2, &mut sizes, 0, &mut |_| {
            seen += 1;
            seen < 3
        });
        assert!(!finished);
        assert_eq!(seen, 3);
    }

    #[test]
    fn numbers_shrink_to_zero_then_closer_and_closer() {
        let n = |k: u32| BigUint::from(k);
        assert_eq!(
            shrink_nat(&n(100)),
            [n(0), n(50), n(75), n(88), n(94), n(97), n(99)]
        );
        assert_eq!(shrink_nat(&n(10)), [n(0), n(5), n(8), n(9)]);
        assert_eq!(shrink_nat(&n(1)), [n(0)]);
        assert_eq!(shrink_nat(&n(2)), [n(0), n(1)]);
        assert!(shrink_nat(&n(0)).is_empty());
    }

    #[test]
    fn the_same_seed_draws_the_same_numbers() {
        let mut a = Rng::new(Rng::seed_of("theorem"));
        let mut b = Rng::new(Rng::seed_of("theorem"));
        let drawn: Vec<usize> = (0..20).map(|_| a.upto(9)).collect();
        assert_eq!(drawn, (0..20).map(|_| b.upto(9)).collect::<Vec<_>>());
        assert!(drawn.iter().all(|k| *k <= 9));
        assert!(drawn.iter().any(|k| *k != drawn[0]));
    }
}

//! Indexed data types in the kernel (docs/proposals/indexed-families.md):
//! index telescopes and result indices (§6.1, §6.2), `case` with
//! unification (§6.3), `Prop` elimination (§6.4), K (§6.5), universes
//! (§6.6), termination (§6.7), evaluation (§6.8) and hashing (§6.9). Each
//! must-reject test of the note's §9 table is here with its paired accepted
//! example, numbered as in the table. The terms are built by hand: the
//! surface syntax comes later.

mod common;

use common::*;
use stitchwort_core::check::{self, DataDecl, infer_closed};
use stitchwort_core::hash::{data_hash, def_hash};
use stitchwort_core::term::Term;
use stitchwort_core::value::{Value, eval, quote};
use stitchwort_core::{DataId, DefId, Globals, Sort, pretty};

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

/// The prelude, with `Vec`, `Fin`, `Le`, an empty `Void` and an empty
/// proposition `FalseP`.
struct Fams {
    p: Prelude,
    vec: DataId,
    fin: DataId,
    le: DataId,
    void: DataId,
    false_p: DataId,
}

impl Fams {
    fn new() -> Fams {
        let mut p = Prelude::new();
        stitchwort_core::native::register_nat(&mut p.g, p.nat).expect("Nat");
        let nat = p.nat_ty();
        // type Vec (a: Type): Nat -> Type =
        //   | VNil: Vec a 0
        //   | VCons [n: Nat] (x: a) (xs: Vec a n): Vec a (Succ n)
        let vec = family(
            &mut p.g,
            "Vec",
            vec![("a", ty())],
            vec![("n", nat.clone())],
            Sort::Type(0),
        );
        let ctors = vec![
            ictor("VNil", vec![], vec![p.num(0)]),
            ictor(
                "VCons",
                vec![
                    ("n", nat.clone()),
                    ("x", v(1)),
                    ("xs", Term::data(vec, vec![v(2), v(1)])),
                ],
                vec![p.succ(v(2))],
            ),
        ];
        check::define_ctors(&mut p.g, vec, ctors).expect("Vec");
        // type Fin: Nat -> Type =
        //   | FZero [n: Nat]: Fin (Succ n)
        //   | FSucc [n: Nat] (i: Fin n): Fin (Succ n)
        let fin = family(
            &mut p.g,
            "Fin",
            vec![],
            vec![("n", nat.clone())],
            Sort::Type(0),
        );
        let ctors = vec![
            ictor("FZero", vec![("n", nat.clone())], vec![p.succ(v(0))]),
            ictor(
                "FSucc",
                vec![("n", nat.clone()), ("i", Term::data(fin, vec![v(0)]))],
                vec![p.succ(v(1))],
            ),
        ];
        check::define_ctors(&mut p.g, fin, ctors).expect("Fin");
        // type Le: Nat -> Nat -> Prop =
        //   | LeZero [n: Nat]: Le 0 n
        //   | LeSucc [m n: Nat] (h: Le m n): Le (Succ m) (Succ n)
        let le = family(
            &mut p.g,
            "Le",
            vec![],
            vec![("m", nat.clone()), ("n", nat.clone())],
            Sort::Prop,
        );
        let ctors = vec![
            ictor("LeZero", vec![("n", nat.clone())], vec![p.num(0), v(0)]),
            ictor(
                "LeSucc",
                vec![
                    ("m", nat.clone()),
                    ("n", nat.clone()),
                    ("h", Term::data(le, vec![v(1), v(0)])),
                ],
                vec![p.succ(v(2)), p.succ(v(1))],
            ),
        ];
        check::define_ctors(&mut p.g, le, ctors).expect("Le");
        let void = data(&mut p.g, "Void", vec![], Sort::Type(0));
        check::define_ctors(&mut p.g, void, vec![]).expect("Void");
        let false_p = data(&mut p.g, "FalseP", vec![], Sort::Prop);
        check::define_ctors(&mut p.g, false_p, vec![]).expect("FalseP");
        Fams {
            p,
            vec,
            fin,
            le,
            void,
            false_p,
        }
    }

    fn g(&mut self) -> &mut Globals {
        &mut self.p.g
    }

    fn nat(&self) -> Term {
        self.p.nat_ty()
    }

    fn vec_ty(&self, a: Term, n: Term) -> Term {
        Term::data(self.vec, vec![a, n])
    }

    fn fin_ty(&self, n: Term) -> Term {
        Term::data(self.fin, vec![n])
    }

    fn le_ty(&self, m: Term, n: Term) -> Term {
        Term::data(self.le, vec![m, n])
    }

    fn vnil(&self) -> Term {
        Term::ctor(self.vec, 0, vec![])
    }

    fn vcons(&self, n: Term, x: Term, xs: Term) -> Term {
        Term::ctor(self.vec, 1, vec![n, x, xs])
    }

    /// Declares and defines a definition that may call itself.
    fn recursive(
        &mut self,
        name: &str,
        ty: Term,
        body: impl FnOnce(&Fams, DefId) -> Term,
    ) -> Result<DefId, &'static str> {
        let id = check::declare_def(self.g(), &name.into(), &ty, false, false, span())
            .map_err(|d| d.code)?;
        let body = body(self, id);
        check::define_def(self.g(), id, &body).map_err(|d| d.code)?;
        Ok(id)
    }

    /// `head: (a: Type) -> (n: Nat) -> Vec a (Succ n) -> a`, with the `VNil`
    /// branch given `nil` (impossible: `None`).
    fn head(&mut self, name: &str, nil: Option<Term>) -> Result<DefId, &'static str> {
        let ty = pi(
            "a",
            ty(),
            pi(
                "n",
                self.nat(),
                pi("v", self.vec_ty(v(1), self.p.succ(v(0))), v(2)),
            ),
        );
        let body = lam(
            "a",
            lam(
                "n",
                lam(
                    "v",
                    icase(
                        0,
                        self.vec,
                        vec![(vec![], nil), (vec!["m", "x", "xs"], Some(v(1)))],
                    ),
                ),
            ),
        );
        define(self.g(), name, ty, body)
    }

    /// `append: (a: Type) -> (n m: Nat) -> Vec a n -> Vec a m -> Vec a (n + m)`.
    fn append(&mut self) -> DefId {
        let ty = pi(
            "a",
            ty(),
            pi(
                "n",
                self.nat(),
                pi(
                    "m",
                    self.nat(),
                    pi(
                        "xs",
                        self.vec_ty(v(2), v(1)),
                        pi(
                            "ys",
                            self.vec_ty(v(3), v(1)),
                            self.vec_ty(v(4), self.p.plus(v(3), v(2))),
                        ),
                    ),
                ),
            ),
        );
        self.recursive("append", ty, |f, id| {
            // In the `VCons` branch: a n m xs ys k x xs'.
            let rest = app(Term::Def(id), [v(7), v(2), v(5), v(0), v(3)]);
            lam(
                "a",
                lam(
                    "n",
                    lam(
                        "m",
                        lam(
                            "xs",
                            lam(
                                "ys",
                                icase(
                                    1,
                                    f.vec,
                                    vec![
                                        (vec![], Some(v(0))),
                                        (
                                            vec!["k", "x", "xs'"],
                                            Some(f.vcons(f.p.plus(v(2), v(5)), v(1), rest)),
                                        ),
                                    ],
                                ),
                            ),
                        ),
                    ),
                ),
            )
        })
        .expect("append")
    }

    /// `replicate: (n: Nat) -> Vec Nat n`, of zeros.
    fn replicate(&mut self) -> DefId {
        let ty = pi("n", self.nat(), self.vec_ty(self.nat(), v(0)));
        self.recursive("replicate", ty, |f, id| {
            lam(
                "n",
                case(
                    0,
                    f.p.nat,
                    vec![
                        (vec![], f.vnil()),
                        (
                            vec!["k"],
                            f.vcons(v(0), f.p.num(0), app(Term::Def(id), [v(0)])),
                        ),
                    ],
                ),
            )
        })
        .expect("replicate")
    }
}

/// The number a closed term computes to.
fn nat_of(g: &Globals, term: &Term) -> Option<usize> {
    let (term, _) = infer_closed(g, term, span()).expect("checks");
    let value = eval(g, &[], &term).unwrap();
    match value {
        Value::Nat(n) => n.to_string().parse().ok(),
        _ => None,
    }
}

// Stage 1: declarations and typing

#[test]
fn families_are_declared_and_typed() {
    let f = Fams::new();
    let nat = f.nat();
    // `Vec Nat 3` is a type; `Vec Nat` alone isn't a full application.
    let vec3 = f.vec_ty(nat.clone(), f.p.num(3));
    assert_eq!(code(infer_closed(&f.p.g, &vec3, span())), "ok");
    let short = Term::data(f.vec, vec![nat.clone()]);
    assert_eq!(code(infer_closed(&f.p.g, &short, span())), "E-MALFORMED");
    // The index is checked against its type.
    let bad_index = f.vec_ty(nat.clone(), Term::ctor(f.p.list, 0, vec![]));
    assert_eq!(
        code(infer_closed(&f.p.g, &bad_index, span())),
        "E-TYPE-MISMATCH"
    );
    // `VNil : Vec Nat 0`, not `Vec Nat 1`.
    let nil0 = Term::Ann(f.vnil().into(), f.vec_ty(nat.clone(), f.p.num(0)).into());
    let nil1 = Term::Ann(f.vnil().into(), f.vec_ty(nat.clone(), f.p.num(1)).into());
    assert_eq!(code(infer_closed(&f.p.g, &nil0, span())), "ok");
    assert_eq!(code(infer_closed(&f.p.g, &nil1, span())), "E-TYPE-MISMATCH");
    // `VCons [0] 7 VNil : Vec Nat 1`, and the implicit field must agree
    // with the tail's length.
    let one = f.vcons(f.p.num(0), f.p.num(7), f.vnil());
    let ok = Term::Ann(one.into(), f.vec_ty(nat.clone(), f.p.num(1)).into());
    assert_eq!(code(infer_closed(&f.p.g, &ok, span())), "ok");
    let wrong = f.vcons(f.p.num(1), f.p.num(7), f.vnil());
    let wrong = Term::Ann(wrong.into(), f.vec_ty(nat.clone(), f.p.num(2)).into());
    assert_eq!(
        code(infer_closed(&f.p.g, &wrong, span())),
        "E-TYPE-MISMATCH"
    );
    // A constructor of a family without parameters infers its type from
    // its result indices: `FZero [2] : Fin 3`.
    let fzero = Term::ctor(f.fin, 0, vec![f.p.num(2)]);
    let (_, ty) = infer_closed(&f.p.g, &fzero, span()).unwrap();
    let ty = quote(&f.p.g, 0, &ty).unwrap();
    assert_eq!(pretty::term(&f.p.g, &[], &ty), "Fin 3");
    // Printing.
    assert_eq!(pretty::term(&f.p.g, &[], &vec3), "Vec Nat 3");
}

#[test]
fn test_8_negative_occurrence_through_an_index_varying_field() {
    // | MkBad (f: Bad 0 -> Void): Bad 1
    let mut f = Fams::new();
    let nat = f.nat();
    let bad = family(f.g(), "Bad", vec![], vec![("n", nat)], Sort::Type(0));
    let field = arrow(
        Term::data(bad, vec![f.p.num(0)]),
        Term::data(f.void, vec![]),
    );
    let ctors = vec![ictor("MkBad", vec![("f", field)], vec![f.p.num(1)])];
    assert_eq!(code(check::define_ctors(f.g(), bad, ctors)), "E-POSITIVITY");
    // Paired: `Vec`, whose `xs: Vec a n` is strictly positive (`Fams::new`).
    assert_eq!(f.p.g.data(f.vec).ctors.len(), 2);
}

#[test]
fn the_group_never_appears_in_indices() {
    // type Q: Prop -> Prop, with a field or a result index mentioning `Q`.
    let mut f = Fams::new();
    let true_p = eq(Some(f.nat()), f.p.num(0), f.p.num(0));
    let q = family(f.g(), "Q", vec![], vec![("p", prop())], Sort::Prop);
    let in_field = Term::data(q, vec![Term::data(q, vec![true_p.clone()])]);
    let ctors = vec![ictor("MkQ", vec![("h", in_field)], vec![true_p.clone()])];
    assert_eq!(code(check::define_ctors(f.g(), q, ctors)), "E-POSITIVITY");
    let q = family(f.g(), "Q2", vec![], vec![("p", prop())], Sort::Prop);
    let in_result = Term::data(q, vec![true_p.clone()]);
    let ctors = vec![ictor("MkQ", vec![], vec![in_result])];
    assert_eq!(code(check::define_ctors(f.g(), q, ctors)), "E-POSITIVITY");
    // Paired: the same with an index that doesn't mention it.
    let q = family(f.g(), "Q3", vec![], vec![("p", prop())], Sort::Prop);
    let fine = Term::data(q, vec![true_p.clone()]);
    let ctors = vec![ictor("MkQ", vec![("h", fine)], vec![true_p])];
    assert_eq!(code(check::define_ctors(f.g(), q, ctors)), "ok");
}

#[test]
fn test_10_a_result_index_of_the_wrong_type() {
    // The kernel's constructor results have no parameters to get wrong
    // (they're always the type's own, §6.1): the surface test of a result
    // `Vec Nat 0` in `Vec (a: Type)` is the elaborator's (stage 3). Here,
    // the kernel's own check: a result index must have its index's type.
    let mut f = Fams::new();
    let nat = f.nat();
    let vec2 = family(
        f.g(),
        "Vec2",
        vec![("a", ty())],
        vec![("n", nat.clone())],
        Sort::Type(0),
    );
    let nil = Term::ctor(f.p.list, 0, vec![]);
    let ctors = vec![ictor("Weird", vec![], vec![nil])];
    assert_eq!(
        code(check::define_ctors(f.g(), vec2, ctors)),
        "E-TYPE-MISMATCH"
    );
    // As many result indices as indices.
    let vec3 = family(
        f.g(),
        "Vec3",
        vec![("a", ty())],
        vec![("n", nat.clone())],
        Sort::Type(0),
    );
    let ctors = vec![ictor("Weird", vec![], vec![])];
    assert_eq!(code(check::define_ctors(f.g(), vec3, ctors)), "E-MALFORMED");
    // Paired: `VNil: Vec a 0`.
    let vec4 = family(
        f.g(),
        "Vec4",
        vec![("a", ty())],
        vec![("n", nat)],
        Sort::Type(0),
    );
    let ctors = vec![ictor("VNil", vec![], vec![f.p.num(0)])];
    assert_eq!(code(check::define_ctors(f.g(), vec4, ctors)), "ok");
}

/// `(p: Type) -> p -> p`.
fn poly_id_ty() -> Term {
    pi("p", ty(), arrow(v(0), v(0)))
}

#[test]
fn test_11_agda_6654_in_type_is_a_universe_error() {
    // type Bad: ((p: Type) -> p -> p) -> Type =
    //   | B (f: (p: Type) -> p -> p): Bad f
    let mut f = Fams::new();
    assert_eq!(
        code(try_family(
            f.g(),
            "Bad",
            vec![],
            vec![("f", poly_id_ty())],
            Sort::Type(0)
        )),
        "E-UNIVERSE"
    );
    // Paired: the same in `Type 1`.
    let bad = family(
        f.g(),
        "Bad1",
        vec![],
        vec![("f", poly_id_ty())],
        Sort::Type(1),
    );
    let ctors = vec![ictor("B", vec![("f", poly_id_ty())], vec![v(0)])];
    assert_eq!(code(check::define_ctors(f.g(), bad, ctors)), "ok");
}

#[test]
fn test_17_a_record_with_indices_is_malformed() {
    let mut f = Fams::new();
    let nat = f.nat();
    let record = |indices| DataDecl {
        name: "R".into(),
        span: span(),
        record: true,
        indices,
    };
    let with_indices = check::declare_indexed_data_group(
        f.g(),
        vec![],
        Sort::Type(0),
        vec![record(vec![("n".into(), nat.clone())])],
    );
    assert_eq!(code(with_indices), "E-MALFORMED");
    // Paired: a record with parameters.
    let with_params = check::declare_indexed_data_group(
        f.g(),
        vec![("a".into(), ty())],
        Sort::Type(0),
        vec![record(vec![])],
    );
    assert_eq!(code(with_params), "ok");
}

/// `type Ty: Type -> sort = | TNat: Ty Nat | TList [b: Type] (t: Ty b): Ty (List b)`.
fn ty_family(f: &mut Fams, name: &str, sort: Sort) -> Result<DataId, &'static str> {
    let d = try_family(f.g(), name, vec![], vec![("t", ty())], sort).map_err(|d| d.code)?;
    let ctors = vec![
        ictor("TNat", vec![], vec![f.nat()]),
        ictor(
            "TList",
            vec![("b", ty()), ("t", Term::data(d, vec![v(0)]))],
            vec![Term::data(f.p.list, vec![v(1)])],
        ),
    ];
    check::define_ctors(f.g(), d, ctors).map_err(|d| d.code)?;
    Ok(d)
}

#[test]
fn test_21_large_indices_are_refused() {
    let mut f = Fams::new();
    assert_eq!(
        ty_family(&mut f, "Ty", Sort::Type(0)).err(),
        Some("E-UNIVERSE")
    );
    // Paired: `Ty: Type -> Type 1`.
    assert!(ty_family(&mut f, "Ty1", Sort::Type(1)).is_ok());
}

#[test]
fn an_index_type_of_a_proposition_may_be_anything() {
    // An index's type obeys the field rule, and anything fits in `Prop`.
    let mut f = Fams::new();
    assert!(try_family(f.g(), "P", vec![], vec![("t", ty_n(3))], Sort::Prop).is_ok());
}

#[test]
fn hashes_cover_indices_and_result_indices() {
    let mut f = Fams::new();
    let nat = f.nat();
    let vec_like = |f: &mut Fams, name: &str, nil: usize| {
        let d = family(
            f.g(),
            name,
            vec![("a", ty())],
            vec![("n", nat.clone())],
            Sort::Type(0),
        );
        let ctors = vec![ictor("VNil", vec![], vec![f.p.num(nil)])];
        check::define_ctors(f.g(), d, ctors).unwrap();
        d
    };
    let (a, b, c) = (
        vec_like(&mut f, "V", 0),
        vec_like(&mut f, "V", 0),
        vec_like(&mut f, "V", 1),
    );
    // The same constructors, without the index.
    let d = data(&mut f.p.g, "V", vec![("a", ty())], Sort::Type(0));
    check::define_ctors(&mut f.p.g, d, vec![ctor("VNil", vec![])]).unwrap();
    let hash = |d| data_hash(&f.p.g, d).unwrap().unwrap();
    assert_eq!(hash(a), hash(b));
    assert_ne!(hash(a), hash(c), "the result index is hashed");
    assert_ne!(hash(a), hash(d), "the index telescope is hashed");
}

// Stage 2: `case`

/// Defines `stuck: ty := body`, which must be refused with `E-INDEX-STUCK`:
/// its label and notes.
fn stuck(g: &mut Globals, ty: Term, body: Term) -> String {
    let id = check::declare_def(g, &"stuck".into(), &ty, false, false, span()).unwrap();
    let e = check::define_def(g, id, &body).unwrap_err();
    assert_eq!(
        e.code, "E-INDEX-STUCK",
        "{}: {:?}",
        e.message, e.labels[0].message
    );
    format!("{} | {}", e.labels[0].message, e.notes.join(" | "))
}

#[test]
fn head_needs_no_vnil_branch() {
    let mut f = Fams::new();
    let head = f.head("head", None).expect("head");
    // head Nat 1 [5, 6] = 5
    let xs = f.vcons(
        f.p.num(1),
        f.p.num(5),
        f.vcons(f.p.num(0), f.p.num(6), f.vnil()),
    );
    let call = app(Term::Def(head), [f.nat(), f.p.num(1), xs]);
    assert_eq!(nat_of(&f.p.g, &call), Some(5));
    // And while running, with erasure.
    let _running = f.p.g.erasure.running();
    let (call, _) = infer_closed(&f.p.g, &call, span()).unwrap();
    let value = eval(&f.p.g, &[], &call).unwrap();
    assert!(matches!(value, Value::Nat(n) if n.to_string() == "5"));
    assert!(def_hash(&f.p.g, head).unwrap().is_some());
}

#[test]
fn test_1_a_possible_branch_marked_impossible() {
    // (a: Type) -> (n: Nat) -> Vec a n -> Nat, with `VCons` marked
    // impossible: it isn't, for a `Vec a n`.
    let mut f = Fams::new();
    let ty = pi(
        "a",
        ty(),
        pi("n", f.nat(), pi("v", f.vec_ty(v(1), v(0)), f.nat())),
    );
    let body = |cons: Option<Term>| {
        lam(
            "a",
            lam(
                "n",
                lam(
                    "v",
                    icase(
                        0,
                        f.vec,
                        vec![(vec![], Some(f.p.num(0))), (vec!["m", "x", "xs"], cons)],
                    ),
                ),
            ),
        )
    };
    let (bad, good) = (body(None), body(Some(f.p.num(1))));
    assert_eq!(
        define(f.g(), "bad", ty.clone(), bad).err(),
        Some("E-MALFORMED")
    );
    // Paired: the same case with a body.
    assert!(define(f.g(), "good", ty, good).is_ok());
}

#[test]
fn test_2_a_body_on_an_impossible_branch() {
    let mut f = Fams::new();
    assert_eq!(f.head("bad", Some(Term::Refl)).err(), Some("E-MALFORMED"));
    // Paired: the branch marked impossible.
    assert!(f.head("head", None).is_ok());
}

/// `get: (a: Type) -> (n: Nat) -> Vec a n -> Fin n -> a`, with the `VNil`
/// branch's body `nil`.
fn get(f: &mut Fams, nil: Option<Term>) -> Result<DefId, &'static str> {
    let ty = pi(
        "a",
        ty(),
        pi(
            "n",
            f.nat(),
            pi("v", f.vec_ty(v(1), v(0)), pi("i", f.fin_ty(v(1)), v(3))),
        ),
    );
    f.recursive("get", ty, |f, id| {
        // In the `VCons` branch: a n v i m x xs, then i's fields.
        let on_i = icase(
            3,
            f.fin,
            vec![
                (vec!["k"], Some(v(2))),
                (
                    vec!["k", "j"],
                    Some(app(Term::Def(id), [v(8), v(4), v(2), v(0)])),
                ),
            ],
        );
        lam(
            "a",
            lam(
                "n",
                lam(
                    "v",
                    lam(
                        "i",
                        icase(
                            1,
                            f.vec,
                            vec![(vec![], nil), (vec!["m", "x", "xs"], Some(on_i))],
                        ),
                    ),
                ),
            ),
        )
    })
}

#[test]
fn test_27_get_with_vnil_marked_impossible() {
    // `VNil` unifies with `Vec a n` (n := 0): it's `i: Fin 0` that's
    // empty, so `VNil`'s branch is a case on `i` with both branches
    // impossible.
    let mut f = Fams::new();
    assert_eq!(get(&mut f, None).err(), Some("E-MALFORMED"));
    // Paired: `VNil`'s body a case on `i: Fin 0` with every branch impossible.
    let mut f = Fams::new();
    let empty_fin = icase(0, f.fin, vec![(vec!["k"], None), (vec!["k", "j"], None)]);
    let get = get(&mut f, Some(empty_fin)).expect("get");
    // get Nat 2 [5, 6] (FSucc [1] (FZero [0])) = 6
    let xs = f.vcons(
        f.p.num(1),
        f.p.num(5),
        f.vcons(f.p.num(0), f.p.num(6), f.vnil()),
    );
    let i = Term::ctor(
        f.fin,
        1,
        vec![f.p.num(1), Term::ctor(f.fin, 0, vec![f.p.num(0)])],
    );
    let call = app(Term::Def(get), [f.nat(), f.p.num(2), xs, i]);
    assert_eq!(nat_of(&f.p.g, &call), Some(6));
}

#[test]
fn test_4_an_index_that_does_not_compute() {
    // (a: Type) -> (n m: Nat) -> Vec a (n + m) -> Nat, matching the vector:
    // `VNil` needs `n + m = 0`, and `n + m` doesn't compute.
    let mut f = Fams::new();
    let ty = pi(
        "a",
        ty(),
        pi(
            "n",
            f.nat(),
            pi(
                "m",
                f.nat(),
                pi("v", f.vec_ty(v(2), f.p.plus(v(1), v(0))), f.nat()),
            ),
        ),
    );
    let on_v = |f: &Fams, ix: usize, nil: Option<Term>| {
        icase(
            ix,
            f.vec,
            vec![(vec![], nil), (vec!["k", "x", "xs"], Some(f.p.num(0)))],
        )
    };
    let lams = |body| lam("a", lam("n", lam("m", lam("v", body))));
    let body = lams(on_v(&f, 0, Some(f.p.num(0))));
    let message = stuck(f.g(), ty.clone(), body);
    assert!(message.contains("needs `n + m = 0`"), "{message}");
    // Paired: the same after matching `n`, so the length computes.
    let split = lams(case(
        2,
        f.p.nat,
        vec![
            (vec![], on_v(&f, 0, Some(f.p.num(0)))),
            (vec!["n'"], on_v(&f, 1, None)),
        ],
    ));
    assert!(define(f.g(), "split", ty, split).is_ok());
    // And `append`, whose goals compute because `+` counts down its first
    // argument.
    let append = f.append();
    let head = f.head("head", None).unwrap();
    let one = |x| f.vcons(f.p.num(0), f.p.num(x), f.vnil());
    let both = app(
        Term::Def(append),
        [f.nat(), f.p.num(1), f.p.num(1), one(3), one(4)],
    );
    let call = app(Term::Def(head), [f.nat(), f.p.num(1), both]);
    assert_eq!(nat_of(&f.p.g, &call), Some(3));
}

#[test]
fn test_5_a_constructor_declared_with_n_plus_one() {
    // `VCons … : Vec a (n + 1)`, matched on a `Vec a (Succ k)`.
    let mut f = Fams::new();
    let nat = f.nat();
    let vec2 = family(
        f.g(),
        "Vec2",
        vec![("a", ty())],
        vec![("n", nat.clone())],
        Sort::Type(0),
    );
    let ctors = vec![
        ictor("VNil", vec![], vec![f.p.num(0)]),
        ictor(
            "VCons",
            vec![
                ("n", nat.clone()),
                ("x", v(1)),
                ("xs", Term::data(vec2, vec![v(2), v(1)])),
            ],
            vec![f.p.plus(v(2), f.p.num(1))],
        ),
    ];
    check::define_ctors(f.g(), vec2, ctors).expect("Vec2");
    let matching = |f: &mut Fams, d: DataId, name: &str| {
        let ty = pi(
            "a",
            ty(),
            pi(
                "k",
                f.nat(),
                pi("v", Term::data(d, vec![v(1), f.p.succ(v(0))]), f.nat()),
            ),
        );
        let body = lam(
            "a",
            lam(
                "k",
                lam(
                    "v",
                    icase(
                        0,
                        d,
                        vec![(vec![], None), (vec!["n", "x", "xs"], Some(f.p.num(0)))],
                    ),
                ),
            ),
        );
        define(f.g(), name, ty, body).err()
    };
    assert_eq!(matching(&mut f, vec2, "stuck"), Some("E-INDEX-STUCK"));
    // Paired: declared `Vec a (Succ n)`.
    let vec = f.vec;
    assert_eq!(matching(&mut f, vec, "fine"), None);
}

#[test]
fn test_6_type_formers_are_not_injective() {
    let mut f = Fams::new();
    let ty1 = ty_family(&mut f, "Ty", Sort::Type(1)).unwrap();
    let branches = || {
        vec![
            (vec![], Some(Term::Nat(std::rc::Rc::new(0u32.into())))),
            (
                vec!["b", "t"],
                Some(Term::Nat(std::rc::Rc::new(1u32.into()))),
            ),
        ]
    };
    // (t: Ty (List Nat)) -> Nat: `TNat` needs `List Nat = Nat` and `TList`
    // `List Nat = List b`, at type `Type`.
    let list_nat = Term::data(f.p.list, vec![f.nat()]);
    let sig = pi("t", Term::data(ty1, vec![list_nat]), f.nat());
    let body = lam("t", icase(0, ty1, branches()));
    let message = stuck(f.g(), sig, body);
    assert!(message.contains("types aren't taken apart"), "{message}");
    // Paired: (c: Type) -> Ty c -> Nat, where `c` is solved.
    let sig = pi("c", ty(), pi("t", Term::data(ty1, vec![v(0)]), f.nat()));
    let body = lam("c", lam("t", icase(0, ty1, branches())));
    assert!(define(f.g(), "fine", sig, body).is_ok());
}

#[test]
fn test_7_occurs_check() {
    // type Loop: Nat -> Nat -> Type = | MkLoop [m: Nat]: Loop m (Succ m)
    let mut f = Fams::new();
    let nat = f.nat();
    let lp = family(
        f.g(),
        "Loop",
        vec![],
        vec![("m", nat.clone()), ("n", nat.clone())],
        Sort::Type(0),
    );
    let ctors = vec![ictor(
        "MkLoop",
        vec![("m", nat.clone())],
        vec![v(0), f.p.succ(v(0))],
    )];
    check::define_ctors(f.g(), lp, ctors).expect("Loop");
    // l: Loop n n gives m := n, then n = Succ n.
    let ty = pi(
        "n",
        nat.clone(),
        pi("l", Term::data(lp, vec![v(0), v(0)]), nat.clone()),
    );
    let body = lam(
        "n",
        lam("l", icase(0, lp, vec![(vec!["m"], Some(f.p.num(0)))])),
    );
    let message = stuck(f.g(), ty, body);
    assert!(message.contains("contain itself"), "{message}");
    // Paired: l: Loop n k.
    let ty = pi(
        "n",
        nat.clone(),
        pi(
            "k",
            nat.clone(),
            pi("l", Term::data(lp, vec![v(1), v(0)]), nat),
        ),
    );
    let body = lam(
        "n",
        lam(
            "k",
            lam("l", icase(0, lp, vec![(vec!["m"], Some(f.p.num(0)))])),
        ),
    );
    assert!(define(f.g(), "fine", ty, body).is_ok());
}

/// `leSuccLe: (m n: Nat) -> Le m n -> Le m (Succ n)`, by structural
/// recursion on the proof.
fn le_succ_le(f: &mut Fams) -> Result<DefId, &'static str> {
    let ty = pi(
        "m",
        f.nat(),
        pi(
            "n",
            f.nat(),
            pi("h", f.le_ty(v(1), v(0)), f.le_ty(v(2), f.p.succ(v(1)))),
        ),
    );
    f.recursive("leSuccLe", ty, |f, id| {
        lam(
            "m",
            lam(
                "n",
                lam(
                    "h",
                    icase(
                        0,
                        f.le,
                        vec![
                            // m := 0, k := n.
                            (vec!["k"], Some(Term::ctor(f.le, 0, vec![f.p.succ(v(2))]))),
                            // m := Succ m', n := Succ n'.
                            (
                                vec!["m'", "n'", "h'"],
                                Some(Term::ctor(
                                    f.le,
                                    1,
                                    vec![
                                        v(2),
                                        f.p.succ(v(1)),
                                        app(Term::Def(id), [v(2), v(1), v(0)]),
                                    ],
                                )),
                            ),
                        ],
                    ),
                ),
            ),
        )
    })
}

#[test]
fn test_12_agda_6654_in_prop_is_a_termination_error() {
    let mut f = Fams::new();
    let false_p = Term::data(f.false_p, vec![]);
    // def IdP: Prop := (p: Prop) -> p -> p
    let id_p_ty = define(f.g(), "IdP", prop(), pi("p", prop(), arrow(v(0), v(0)))).unwrap();
    let id_p_ty = Term::Def(id_p_ty);
    // type Bad: IdP -> Prop = | B (f: IdP): Bad f
    let bad = family(
        f.g(),
        "Bad",
        vec![],
        vec![("x", id_p_ty.clone())],
        Sort::Prop,
    );
    let ctors = vec![ictor("B", vec![("f", id_p_ty.clone())], vec![v(0)])];
    check::define_ctors(f.g(), bad, ctors).expect("Bad");
    // def idP: IdP := p h => h; def bad: Bad idP := B idP
    let id_p = define(f.g(), "idP", id_p_ty.clone(), lam("p", lam("h", v(0)))).unwrap();
    let bad_idp = Term::data(bad, vec![Term::Def(id_p)]);
    let bad_value = define(
        f.g(),
        "bad",
        bad_idp.clone(),
        Term::ctor(bad, 0, vec![Term::Def(id_p)]),
    )
    .unwrap();
    // theorem noBad [x: IdP]: Bad x -> FalseP
    //   | B f => noBad [idP] (f (Bad idP) bad)
    // The index equation `x = f`, at `IdP`, is a variable solution.
    let ty = pi("x", id_p_ty, pi("b", Term::data(bad, vec![v(0)]), false_p));
    let result = f.recursive("noBad", ty, |_, id| {
        let smaller = app(v(0), [bad_idp.clone(), Term::Def(bad_value)]);
        lam(
            "x",
            lam(
                "b",
                icase(
                    0,
                    bad,
                    vec![(
                        vec!["f"],
                        Some(app(Term::Def(id), [Term::Def(id_p), smaller])),
                    )],
                ),
            ),
        )
    });
    assert_eq!(result.err(), Some("E-TERMINATION"));
    // Paired: structural recursion on a proof of `Le`.
    assert!(le_succ_le(&mut f).is_ok());
}

#[test]
fn test_13_no_descent_from_a_solved_index() {
    // def down [n: Nat]: Vec Nat n -> Nat
    //   | VNil => 0
    //   | VCons [n := m] _ _ => down [m] (replicate m)
    let mut f = Fams::new();
    let replicate = f.replicate();
    let down = |f: &mut Fams, name: &str, recurse: Term| {
        let ty = pi("n", f.nat(), pi("v", f.vec_ty(f.nat(), v(0)), f.nat()));
        f.recursive(name, ty, |f, id| {
            lam(
                "n",
                lam(
                    "v",
                    icase(
                        0,
                        f.vec,
                        vec![
                            (vec![], Some(f.p.num(0))),
                            (
                                vec!["m", "x", "xs"],
                                Some(app(Term::Def(id), [v(2), recurse])),
                            ),
                        ],
                    ),
                ),
            )
        })
        .err()
    };
    let rebuilt = app(Term::Def(replicate), [v(2)]);
    assert_eq!(down(&mut f, "down", rebuilt), Some("E-TERMINATION"));
    // Paired: the same recursing on `xs`.
    assert_eq!(down(&mut f, "down2", v(0)), None);
}

/// `type IsSucc: Nat -> Prop = | MkIsSucc [n: Nat]: IsSucc (Succ n)`.
fn is_succ(f: &mut Fams) -> DataId {
    let nat = f.nat();
    let d = family(
        f.g(),
        "IsSucc",
        vec![],
        vec![("k", nat.clone())],
        Sort::Prop,
    );
    let ctors = vec![ictor("MkIsSucc", vec![("n", nat)], vec![f.p.succ(v(0))])];
    check::define_ctors(f.g(), d, ctors).expect("IsSucc");
    d
}

#[test]
fn test_14_prop_elimination_through_an_index_field() {
    // pred: IsSucc k -> Nat, reading `n`.
    let mut f = Fams::new();
    let is_succ = is_succ(&mut f);
    let ty = pi(
        "k",
        f.nat(),
        pi("h", Term::data(is_succ, vec![v(0)]), f.nat()),
    );
    let body = lam(
        "k",
        lam("h", icase(0, is_succ, vec![(vec!["n"], Some(v(0)))])),
    );
    assert_eq!(define(f.g(), "pred", ty, body).err(), Some("E-PROP-ELIM"));
    // Paired: IsSucc k -> Le 1 k, a proposition.
    let ty = pi(
        "k",
        f.nat(),
        pi(
            "h",
            Term::data(is_succ, vec![v(0)]),
            f.le_ty(f.p.num(1), v(1)),
        ),
    );
    let proof = Term::ctor(
        f.le,
        1,
        vec![f.p.num(0), v(0), Term::ctor(f.le, 0, vec![v(0)])],
    );
    let body = lam(
        "k",
        lam("h", icase(0, is_succ, vec![(vec!["n"], Some(proof))])),
    );
    assert!(define(f.g(), "positive", ty, body).is_ok());
}

#[test]
fn test_15_prop_elimination_with_two_constructors() {
    // Le m n -> Nat, by matching.
    let mut f = Fams::new();
    let ty = pi(
        "m",
        f.nat(),
        pi("n", f.nat(), pi("h", f.le_ty(v(1), v(0)), f.nat())),
    );
    let body = lam(
        "m",
        lam(
            "n",
            lam(
                "h",
                icase(
                    0,
                    f.le,
                    vec![
                        (vec!["k"], Some(f.p.num(0))),
                        (vec!["m'", "n'", "h'"], Some(f.p.num(1))),
                    ],
                ),
            ),
        ),
    );
    assert_eq!(define(f.g(), "bad", ty, body).err(), Some("E-PROP-ELIM"));
    // Paired: Le (Succ n) 0 -> Nat, where every branch is impossible.
    let ty = pi(
        "n",
        f.nat(),
        pi("h", f.le_ty(f.p.succ(v(0)), f.p.num(0)), f.nat()),
    );
    let body = lam(
        "n",
        lam(
            "h",
            icase(
                0,
                f.le,
                vec![(vec!["k"], None), (vec!["m'", "n'", "h'"], None)],
            ),
        ),
    );
    assert!(define(f.g(), "absurd", ty, body).is_ok());
}

#[test]
fn test_19_dependent_constructor_injectivity() {
    // type W: Type = | Mk (n: Nat) (i: Fin (Succ n))
    let mut f = Fams::new();
    let nat = f.nat();
    let w = data(f.g(), "W", vec![], Sort::Type(0));
    let fields = vec![("n", nat.clone()), ("i", f.fin_ty(f.p.succ(v(0))))];
    check::define_ctors(f.g(), w, vec![ctor("Mk", fields)]).expect("W");
    let mk = |n, i| Term::ctor(w, 0, vec![n, i]);
    // An opaque `g`: stuck on a variable.
    let g_body = lam(
        "x",
        case(0, f.p.nat, vec![(vec![], f.p.num(0)), (vec!["k"], v(0))]),
    );
    let g_fn = define(f.g(), "g", arrow(nat.clone(), nat.clone()), g_body).unwrap();
    // type Q: W -> Type = | MkQ [m: Nat] [j: Fin (Succ (Succ m))]: Q (Mk (Succ m) j)
    let q = family(
        f.g(),
        "Q",
        vec![],
        vec![("w", Term::data(w, vec![]))],
        Sort::Type(0),
    );
    let ctors = vec![ictor(
        "MkQ",
        vec![
            ("m", nat.clone()),
            ("j", f.fin_ty(f.p.succ(f.p.succ(v(0))))),
        ],
        vec![mk(f.p.succ(v(1)), v(0))],
    )];
    check::define_ctors(f.g(), q, ctors).expect("Q");
    // (k: Nat) -> (i: Fin (Succ (g k))) -> Q (Mk (g k) i) -> Nat: the first
    // fields give `g k = Succ m`, stuck; the unifier must stop there.
    let ty = pi(
        "k",
        nat.clone(),
        pi(
            "i",
            f.fin_ty(f.p.succ(app(Term::Def(g_fn), [v(0)]))),
            pi(
                "q",
                Term::data(q, vec![mk(app(Term::Def(g_fn), [v(1)]), v(0))]),
                nat.clone(),
            ),
        ),
    );
    let body = lam(
        "k",
        lam(
            "i",
            lam("q", icase(0, q, vec![(vec!["m", "j"], Some(f.p.num(0)))])),
        ),
    );
    let message = stuck(f.g(), ty, body);
    assert!(message.contains("needs `g k = Succ m`"), "{message}");
    // Paired: type P: W -> Type = | MkP [m: Nat] [j: Fin (Succ m)]: P (Mk m j),
    // matching p: P (Mk n i): m := n first, then j := i at `Fin (Succ n)`.
    let pw = family(
        f.g(),
        "P",
        vec![],
        vec![("w", Term::data(w, vec![]))],
        Sort::Type(0),
    );
    let ctors = vec![ictor(
        "MkP",
        vec![("m", nat.clone()), ("j", f.fin_ty(f.p.succ(v(0))))],
        vec![mk(v(1), v(0))],
    )];
    check::define_ctors(f.g(), pw, ctors).expect("P");
    let ty = pi(
        "n",
        nat.clone(),
        pi(
            "i",
            f.fin_ty(f.p.succ(v(0))),
            pi(
                "p",
                Term::data(pw, vec![mk(v(1), v(0))]),
                f.fin_ty(f.p.succ(v(2))),
            ),
        ),
    );
    // In the branch, `j` is `i`, at `i`'s type.
    let body = lam(
        "n",
        lam(
            "i",
            lam("p", icase(0, pw, vec![(vec!["m", "j"], Some(v(0)))])),
        ),
    );
    assert!(define(f.g(), "fine", ty, body).is_ok());
}

#[test]
fn test_20_a_refined_outer_hypothesis() {
    // (P: Nat -> Type) (a: Type) (n: Nat) (h: P n) (v: Vec a n) -> P n, and
    // in the `VCons [n := m] _ _` branch, `h: P (Succ m)`.
    let mut f = Fams::new();
    let nat = f.nat();
    let ty = pi(
        "P",
        arrow(nat.clone(), ty()),
        pi(
            "a",
            ty(),
            pi(
                "n",
                nat.clone(),
                pi(
                    "h",
                    app(v(2), [v(0)]),
                    pi("v", f.vec_ty(v(2), v(1)), app(v(4), [v(2)])),
                ),
            ),
        ),
    );
    // In the branch: P a n h v m x xs.
    let body = |f: &Fams, at: Term| {
        lam(
            "P",
            lam(
                "a",
                lam(
                    "n",
                    lam(
                        "h",
                        lam(
                            "v",
                            icase(
                                0,
                                f.vec,
                                vec![
                                    (vec![], Some(v(1))),
                                    (
                                        vec!["m", "x", "xs"],
                                        Some(Term::Ann(v(4).into(), app(v(7), [at]).into())),
                                    ),
                                ],
                            ),
                        ),
                    ),
                ),
            ),
        )
    };
    // `h` where a `P m` is expected.
    let wrong = body(&f, v(2));
    let id = check::declare_def(f.g(), &"wrong".into(), &ty, false, false, span()).unwrap();
    let error = check::define_def(f.g(), id, &wrong).unwrap_err();
    assert_eq!(error.code, "E-TYPE-MISMATCH");
    // The message shows `h`'s type quoted at the branch's depth: the
    // well-scoped `P (Succ m)`, naming the field `m`.
    let label = &error.labels[0].message;
    assert!(label.contains("expected `P m`"), "{label}");
    assert!(label.contains("this has type `P (Succ m)`"), "{label}");
    // Paired: `h` where a `P (Succ m)` is expected.
    let right = body(&f, f.p.succ(v(2)));
    assert!(define(f.g(), "right", ty, right).is_ok());
}

/// `type P: sort = | A | B`.
fn two(f: &mut Fams, name: &str, sort: Sort) -> DataId {
    let d = data(f.g(), name, vec![], sort);
    check::define_ctors(f.g(), d, vec![ctor("A", vec![]), ctor("B", vec![])]).unwrap();
    d
}

#[test]
fn test_22_no_conflict_between_proofs() {
    // type P: Prop = | A | B
    // type SameP (x: P): P -> Prop = | R: SameP x x
    // theorem noAB: SameP A B -> FalseP | ()
    let no_ab = |sort| {
        let mut f = Fams::new();
        let p = two(&mut f, "P", sort);
        let same = family(
            f.g(),
            "SameP",
            vec![("x", Term::data(p, vec![]))],
            vec![("y", Term::data(p, vec![]))],
            Sort::Prop,
        );
        check::define_ctors(f.g(), same, vec![ictor("R", vec![], vec![v(0)])]).unwrap();
        let (a, b) = (Term::ctor(p, 0, vec![]), Term::ctor(p, 1, vec![]));
        let ty = pi(
            "s",
            Term::data(same, vec![a, b]),
            Term::data(f.false_p, vec![]),
        );
        let body = lam("s", icase(0, same, vec![(vec![], None)]));
        define(f.g(), "noAB", ty, body).err()
    };
    assert_eq!(no_ab(Sort::Prop), Some("E-INDEX-STUCK"));
    // Paired: `P: Type`, where `B = A` is a conflict.
    assert_eq!(no_ab(Sort::Type(0)), None);
}

#[test]
fn test_23_no_injectivity_for_proofs() {
    // type Hidden: Prop = | Hide (n: Nat), a family indexed by it, and an
    // empty match needing `Hide 1 = Hide 0`.
    let empty = |sort| {
        let mut f = Fams::new();
        let nat = f.nat();
        let hidden = data(f.g(), "Hidden", vec![], sort);
        check::define_ctors(f.g(), hidden, vec![ctor("Hide", vec![("n", nat)])]).unwrap();
        let hide = |n| Term::ctor(hidden, 0, vec![n]);
        let hf = family(
            f.g(),
            "HF",
            vec![],
            vec![("h", Term::data(hidden, vec![]))],
            Sort::Prop,
        );
        let ctors = vec![ictor("MkHF", vec![], vec![hide(f.p.num(0))])];
        check::define_ctors(f.g(), hf, ctors).unwrap();
        let ty = pi(
            "x",
            Term::data(hf, vec![hide(f.p.num(1))]),
            Term::data(f.false_p, vec![]),
        );
        let body = lam("x", icase(0, hf, vec![(vec![], None)]));
        define(f.g(), "empty", ty, body).err()
    };
    assert_eq!(empty(Sort::Prop), Some("E-INDEX-STUCK"));
    // Paired: `Hidden: Type`, by injectivity, then `1 = 0`.
    assert_eq!(empty(Sort::Type(0)), None);
}

#[test]
fn test_25_a_proof_field_before_data() {
    // type T: Type = | MkT (h: P) (n: Nat), with `P: Prop = A | B`.
    let mut f = Fams::new();
    let nat = f.nat();
    let p = two(&mut f, "P", Sort::Prop);
    let t = data(f.g(), "T", vec![], Sort::Type(0));
    let fields = vec![("h", Term::data(p, vec![])), ("n", nat)];
    check::define_ctors(f.g(), t, vec![ctor("MkT", fields)]).unwrap();
    let mk_t = |h, n| Term::ctor(t, 0, vec![h, n]);
    let (a, b) = (Term::ctor(p, 0, vec![]), Term::ctor(p, 1, vec![]));
    let false_p = Term::data(f.false_p, vec![]);
    // A family whose only constructor is `MkTF: TF (MkT B 1)`.
    let tf = family(
        f.g(),
        "TF",
        vec![],
        vec![("t", Term::data(t, vec![]))],
        Sort::Prop,
    );
    let ctors = vec![ictor("MkTF", vec![], vec![mk_t(b, f.p.num(1))])];
    check::define_ctors(f.g(), tf, ctors).unwrap();
    // An empty match needing `MkT A 0 = MkT B 1`: stuck at `A = B`, never
    // impossible from the later `0 = 1`.
    let ty = pi(
        "x",
        Term::data(tf, vec![mk_t(a.clone(), f.p.num(0))]),
        false_p.clone(),
    );
    let body = lam("x", icase(0, tf, vec![(vec![], None)]));
    let message = stuck(f.g(), ty, body);
    assert!(message.contains("needs `A = B`"), "{message}");
    assert!(message.contains("proofs"), "{message}");
    // Paired: `MkT h 0 = MkT A 1` with `h` a variable: `h := A`, then
    // `0 = 1`, impossible.
    let tg = family(
        f.g(),
        "TG",
        vec![],
        vec![("t", Term::data(t, vec![]))],
        Sort::Prop,
    );
    let ctors = vec![ictor("MkTG", vec![], vec![mk_t(a, f.p.num(1))])];
    check::define_ctors(f.g(), tg, ctors).unwrap();
    let ty = pi(
        "h",
        Term::data(p, vec![]),
        pi("x", Term::data(tg, vec![mk_t(v(0), f.p.num(0))]), false_p),
    );
    let body = lam("h", lam("x", icase(0, tg, vec![(vec![], None)])));
    assert!(define(f.g(), "fine", ty, body).is_ok());
}

#[test]
fn same_k_is_accepted() {
    // type Same (a: Type) (x: a): a -> Prop = | Refl: Same a x x
    // theorem sameK (p: Same a x x): p = Refl | Refl => rfl
    let mut f = Fams::new();
    let same = family(
        f.g(),
        "Same",
        vec![("a", ty()), ("x", v(0))],
        vec![("y", v(1))],
        Sort::Prop,
    );
    check::define_ctors(f.g(), same, vec![ictor("Refl", vec![], vec![v(0)])]).unwrap();
    let ty = pi(
        "a",
        ty(),
        pi(
            "x",
            v(0),
            pi(
                "p",
                Term::data(same, vec![v(1), v(0), v(0)]),
                eq(
                    Some(Term::data(same, vec![v(2), v(1), v(1)])),
                    v(0),
                    Term::ctor(same, 0, vec![]),
                ),
            ),
        ),
    );
    // The index equation is `x = x`: deleted (axiom K).
    let body = lam(
        "a",
        lam(
            "x",
            lam("p", icase(0, same, vec![(vec![], Some(Term::Refl))])),
        ),
    );
    let id = check::declare_def(f.g(), &"sameK".into(), &ty, true, false, span()).unwrap();
    assert_eq!(code(check::define_def(f.g(), id, &body)), "ok");
}

#[test]
fn an_impossible_branch_is_never_taken() {
    // `head Nat 0 VNil` is ill-typed, so evaluating it directly reaches
    // the impossible branch: checking leaves the definition folded.
    let mut f = Fams::new();
    let head = f.head("head", None).unwrap();
    let call = app(Term::Def(head), [f.nat(), f.p.num(0), f.vnil()]);
    let value = eval(&f.p.g, &[], &call).unwrap();
    assert!(matches!(value, Value::Neutral(..)));
}

#[test]
#[should_panic(expected = "unreachable")]
fn running_into_an_impossible_branch_fails_loudly() {
    let mut f = Fams::new();
    let head = f.head("head", None).unwrap();
    let call = app(Term::Def(head), [f.nat(), f.p.num(0), f.vnil()]);
    let _running = f.p.g.erasure.running();
    let _ = eval(&f.p.g, &[], &call);
}

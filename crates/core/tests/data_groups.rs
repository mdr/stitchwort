//! Groups of data types whose constructors mention each other
//! (docs/proposals/mutual-recursion.md §5.4, §5.5, §7, §8.4): one shared
//! parameter telescope and universe, admission of every member's
//! constructors at once, positivity across the group, no elimination into
//! data from a group of propositions, termination over the group, and
//! hashing it as a unit. These call the kernel directly, in orders the
//! elaborator never uses.

mod common;

use std::rc::Rc;

use common::*;
use stitchwort_core::check::{self, CtorDecl, declare_data_group, define_data_group};
use stitchwort_core::globals::State;
use stitchwort_core::hash::{ContentHash, data_hash, def_hash};
use stitchwort_core::term::Term;
use stitchwort_core::value::{eval, quote};
use stitchwort_core::{DataId, DefId, Globals, Name, Sort};

fn code<T>(r: Result<T, stitchwort_syntax::Diagnostic>) -> &'static str {
    r.err().map_or("ok", |d| d.code)
}

/// Declares a group with these names, parameters and universe.
fn group(g: &mut Globals, names: &[&str], params: Vec<(&str, Term)>, sort: Sort) -> Vec<DataId> {
    try_group(g, names, params, sort).expect("the group's parameters check")
}

fn try_group(
    g: &mut Globals,
    names: &[&str],
    params: Vec<(&str, Term)>,
    sort: Sort,
) -> Result<Vec<DataId>, stitchwort_syntax::Diagnostic> {
    declare_data_group(
        g,
        params.into_iter().map(|(x, t)| (x.into(), t)).collect(),
        sort,
        names.iter().map(|n| (Name::from(*n), span())).collect(),
    )
}

fn state(g: &Globals, d: DataId) -> State {
    g.data(d).state
}

/// `Tree = Node (label : Nat) (kids : Forest)`,
/// `Forest = FNil | FCons (first : Tree) (rest : Forest)`.
fn tree_forest_ctors(p: &Prelude, tree: DataId, forest: DataId) -> Vec<(DataId, Vec<CtorDecl>)> {
    let (t, f) = (Term::Data(tree, vec![]), Term::Data(forest, vec![]));
    vec![
        (
            tree,
            vec![ctor(
                "Node",
                vec![("label", p.nat_ty()), ("kids", f.clone())],
            )],
        ),
        (
            forest,
            vec![
                ctor("FNil", vec![]),
                ctor("FCons", vec![("first", t), ("rest", f)]),
            ],
        ),
    ]
}

/// A final `Tree`/`Forest` group.
fn tree_forest(p: &mut Prelude) -> (DataId, DataId) {
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let ctors = tree_forest_ctors(p, ids[0], ids[1]);
    define_data_group(&mut p.g, ctors).expect("Tree and Forest");
    (ids[0], ids[1])
}

/// `size (Node l kids) = Succ (sizeForest kids)`,
/// `sizeForest FNil = 0; sizeForest (FCons t ts) = size t + sizeForest ts`.
fn size_bodies(
    p: &Prelude,
    tree: DataId,
    forest: DataId,
    size: DefId,
    sf: DefId,
) -> Vec<(DefId, Term)> {
    let succ = |t: Term| Term::ctor(p.nat, 1, vec![t]);
    vec![
        (
            size,
            lam(
                "t",
                case(
                    0,
                    tree,
                    vec![(vec!["label", "kids"], succ(app(Term::Def(sf), [v(0)])))],
                ),
            ),
        ),
        (
            sf,
            lam(
                "ts",
                case(
                    0,
                    forest,
                    vec![
                        (vec![], p.num(0)),
                        (
                            vec!["first", "rest"],
                            p.plus(app(Term::Def(size), [v(1)]), app(Term::Def(sf), [v(0)])),
                        ),
                    ],
                ),
            ),
        ),
    ]
}

/// Evaluates a closed term to a number.
fn number(g: &Globals, term: &Term) -> Option<usize> {
    let (term, _) = check::infer_closed(g, term, span()).ok()?;
    let value = eval(g, &[], &term).ok()?;
    nat_of(&quote(g, 0, &value).ok()?)
}

fn nat_of(term: &Term) -> Option<usize> {
    match term.strip_loc() {
        Term::Ctor(_, 0, _) => Some(0),
        Term::Ctor(_, 1, args) => nat_of(&args[0]).map(|n| n + 1),
        Term::Nat(n) => usize::try_from(&**n).ok(),
        _ => None,
    }
}

#[test]
fn a_tree_and_a_forest_are_admitted_together() {
    let mut p = Prelude::new();
    let (tree, forest) = tree_forest(&mut p);
    for d in [tree, forest] {
        assert_eq!(state(&p.g, d), State::Final);
        assert_eq!(&*p.g.data(d).group, &[tree, forest]);
    }
    // Functions over them, by structural recursion across the group.
    let nat = p.nat_ty();
    let ty = |d: DataId| arrow(Term::Data(d, vec![]), nat.clone());
    let size = declare(&mut p.g, "size", ty(tree));
    let sf = declare(&mut p.g, "sizeForest", ty(forest));
    let bodies = size_bodies(&p, tree, forest, size, sf);
    assert_eq!(code(check::define_group(&mut p.g, &bodies)), "ok");
    // Node 0 (FCons (Node 0 FNil) (FCons (Node 0 FNil) FNil)): three nodes.
    let leaf = || Term::ctor(tree, 0, vec![p.num(0), Term::ctor(forest, 0, vec![])]);
    let cons = |t: Term, ts: Term| Term::ctor(forest, 1, vec![t, ts]);
    let kids = cons(leaf(), cons(leaf(), Term::ctor(forest, 0, vec![])));
    let example = Term::ctor(tree, 0, vec![p.num(0), kids]);
    let annotated = Term::Ann(Rc::new(example), Rc::new(Term::Data(tree, vec![])));
    assert_eq!(number(&p.g, &app(Term::Def(size), [annotated])), Some(3));
}

#[test]
fn rebuilding_a_tree_from_a_forest_does_not_terminate() {
    // bad t = badForest (FCons t FNil); badForest (FCons t ts) = bad t; …
    let mut p = Prelude::new();
    let (tree, forest) = tree_forest(&mut p);
    let nat = p.nat_ty();
    let ty = |d: DataId| arrow(Term::Data(d, vec![]), nat.clone());
    let bad = declare(&mut p.g, "bad", ty(tree));
    let bad_forest = declare(&mut p.g, "badForest", ty(forest));
    let wrap = Term::ctor(forest, 1, vec![v(0), Term::ctor(forest, 0, vec![])]);
    let bodies = vec![
        (bad, lam("t", app(Term::Def(bad_forest), [wrap]))),
        (
            bad_forest,
            lam(
                "ts",
                case(
                    0,
                    forest,
                    vec![
                        (vec![], p.num(0)),
                        (vec!["first", "rest"], app(Term::Def(bad), [v(1)])),
                    ],
                ),
            ),
        ),
    ];
    assert_eq!(
        code(check::define_group(&mut p.g, &bodies)),
        "E-TERMINATION"
    );
}

/// `Bad1 = MkBad1 (f : Bad2 -> Void)`, `Bad2 = MkBad2 (b : Bad1)`.
fn bad_ctors(void: DataId, bad1: DataId, bad2: DataId) -> Vec<(DataId, Vec<CtorDecl>)> {
    vec![
        (
            bad1,
            vec![ctor(
                "MkBad1",
                vec![(
                    "f",
                    arrow(Term::Data(bad2, vec![]), Term::Data(void, vec![])),
                )],
            )],
        ),
        (
            bad2,
            vec![ctor("MkBad2", vec![("b", Term::Data(bad1, vec![]))])],
        ),
    ]
}

fn make_void(p: &mut Prelude) -> DataId {
    let void = data(&mut p.g, "Void", vec![], Sort::Prop);
    check::define_ctors(&mut p.g, void, vec![]).unwrap();
    void
}

#[test]
fn a_negative_occurrence_through_a_sibling_is_refused() {
    // Each looks positive on its own; together they would prove `Void`:
    // notBad (MkBad1 f) = f (MkBad2 (MkBad1 f)), and notBad (MkBad1
    // unwrap), where unwrap (MkBad2 b) = notBad b. Neither is recursive.
    let mut p = Prelude::new();
    let void = make_void(&mut p);
    let ids = group(&mut p.g, &["Bad1", "Bad2"], vec![], Sort::Type(0));
    let r = define_data_group(&mut p.g, bad_ctors(void, ids[0], ids[1]));
    let e = r.unwrap_err();
    assert_eq!(e.code, "E-POSITIVITY");
    assert_eq!(e.message, "`Bad2` is used in a negative position");
    // Every member failed: no constructors, no matches, no hash.
    for d in &ids {
        assert_eq!(state(&p.g, *d), State::Failed);
        assert!(p.g.data(*d).ctors.is_empty());
        assert_eq!(data_hash(&p.g, *d).unwrap(), None);
    }
    let to_void = arrow(Term::Data(ids[0], vec![]), Term::Data(void, vec![]));
    // (Refused as a match on a type that isn't finished.)
    let r = define(
        &mut p.g,
        "notBad",
        to_void,
        lam("x", case(0, ids[0], vec![])),
    );
    assert_eq!(r.err(), Some("E-MALFORMED"));

    // Nor can it be split in two: `Bad1` alone mentions `Bad2`, which isn't
    // finished.
    let mut p = Prelude::new();
    let void = make_void(&mut p);
    let bad1 = data(&mut p.g, "Bad1", vec![], Sort::Type(0));
    let bad2 = data(&mut p.g, "Bad2", vec![], Sort::Type(0));
    let mut ctors = bad_ctors(void, bad1, bad2);
    let second = ctors.pop().unwrap();
    let first = ctors.pop().unwrap();
    assert_eq!(
        code(define_data_group(&mut p.g, vec![first])),
        "E-MALFORMED"
    );
    assert_eq!(
        code(define_data_group(&mut p.g, vec![second])),
        "E-FAILED-DEPENDENCY"
    );

    // Or the other way round: `Bad2` first, mentioning `Bad1`.
    let mut p = Prelude::new();
    let void = make_void(&mut p);
    let bad1 = data(&mut p.g, "Bad1", vec![], Sort::Type(0));
    let bad2 = data(&mut p.g, "Bad2", vec![], Sort::Type(0));
    let mut ctors = bad_ctors(void, bad1, bad2);
    let second = ctors.pop().unwrap();
    assert_eq!(
        code(define_data_group(&mut p.g, vec![second])),
        "E-MALFORMED"
    );
}

#[test]
fn every_member_must_be_strictly_positive_in_every_member() {
    let mut p = Prelude::new();
    let nat = p.nat_ty();
    // A sibling in the input of a function, in the codomain's input, under
    // another type, and with other parameters.
    let list = p.list;
    let n = || nat.clone();
    let cases: Vec<Box<dyn Fn(DataId, DataId) -> Term>> = vec![
        Box::new(|_, b| arrow(Term::Data(b, vec![]), n())),
        Box::new(|_, b| arrow(n(), arrow(Term::Data(b, vec![]), n()))),
        Box::new(|_, b| Term::data(list, vec![Term::Data(b, vec![])])),
    ];
    for (k, field) in cases.iter().enumerate() {
        let mut g = Prelude::new().g;
        let ids = group(&mut g, &["A", "B"], vec![], Sort::Type(0));
        let fields = vec![
            (
                ids[0],
                vec![ctor("MkA", vec![("x", field(ids[0], ids[1]))])],
            ),
            (
                ids[1],
                vec![ctor("MkB", vec![("a", Term::Data(ids[0], vec![]))])],
            ),
        ];
        assert_eq!(
            code(define_data_group(&mut g, fields)),
            "E-POSITIVITY",
            "case {k}"
        );
        assert_eq!(state(&g, ids[1]), State::Failed);
    }
    // With a parameter: a sibling applied to something else.
    let ids = group(&mut p.g, &["A", "B"], vec![("a", ty())], Sort::Type(0));
    let fields = vec![
        (
            ids[0],
            vec![ctor("MkA", vec![("x", Term::data(ids[1], vec![n()]))])],
        ),
        (
            ids[1],
            vec![ctor("MkB", vec![("y", Term::data(ids[0], vec![v(0)]))])],
        ),
    ];
    assert_eq!(code(define_data_group(&mut p.g, fields)), "E-POSITIVITY");
    // Neighbour: siblings applied to the parameter, as fields and as the
    // result of a function field.
    let ids = group(&mut p.g, &["C", "D"], vec![("a", ty())], Sort::Type(0));
    let fields = vec![
        (
            ids[0],
            vec![ctor(
                "MkC",
                vec![
                    ("x", v(0)),
                    ("ds", arrow(n(), Term::data(ids[1], vec![v(1)]))),
                ],
            )],
        ),
        (
            ids[1],
            vec![
                ctor("Stop", vec![]),
                ctor("MkD", vec![("c", Term::data(ids[0], vec![v(0)]))]),
            ],
        ),
    ];
    assert_eq!(code(define_data_group(&mut p.g, fields)), "ok");
}

#[test]
fn a_pending_member_is_not_empty_and_has_no_constructors() {
    let mut p = Prelude::new();
    let void = make_void(&mut p);
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let (tree, forest) = (ids[0], ids[1]);
    // A signature mentioning a pending member is refused.
    let tree_to_void = arrow(Term::Data(tree, vec![]), Term::Data(void, vec![]));
    let r = check::declare_def(
        &mut p.g,
        &"impossible".into(),
        &tree_to_void,
        false,
        false,
        span(),
    );
    assert_eq!(code(r), "E-MALFORMED");
    // An empty match on one, checked directly, is refused.
    let absurd = Term::Ann(
        Rc::new(lam("x", case(0, tree, vec![]))),
        Rc::new(tree_to_void.clone()),
    );
    assert_eq!(
        code(check::infer_closed(&p.g, &absurd, span())),
        "E-MALFORMED"
    );
    // A constructor of one doesn't exist yet.
    let fnil = Term::Ann(
        Rc::new(Term::ctor(forest, 0, vec![])),
        Rc::new(Term::Data(forest, vec![])),
    );
    assert_eq!(
        code(check::infer_closed(&p.g, &fnil, span())),
        "E-MALFORMED"
    );
    // No hash.
    assert_eq!(data_hash(&p.g, tree).unwrap(), None);
    // Once the group is final, all of these work, at once.
    let ctors = tree_forest_ctors(&p, tree, forest);
    define_data_group(&mut p.g, ctors).unwrap();
    assert_eq!(code(check::infer_closed(&p.g, &fnil, span())), "ok");
    assert!(data_hash(&p.g, tree).unwrap().is_some());
    assert!(data_hash(&p.g, forest).unwrap().is_some());
    // And `impossible` is just not exhaustive.
    let r = define(
        &mut p.g,
        "impossible",
        tree_to_void,
        lam("x", case(0, tree, vec![])),
    );
    assert_eq!(r.err(), Some("E-NONEXHAUSTIVE"));
}

#[test]
fn a_group_is_defined_whole_or_not_at_all() {
    // Only some of the members: refused, and every member fails.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let mut ctors = tree_forest_ctors(&p, ids[0], ids[1]);
    ctors.pop();
    let e = define_data_group(&mut p.g, ctors).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
    assert!(
        e.labels[0]
            .message
            .contains("`Forest` was declared in this group"),
        "{:?}",
        e.labels
    );
    assert_eq!(state(&p.g, ids[0]), State::Failed);
    assert_eq!(state(&p.g, ids[1]), State::Failed);

    // A member listed twice.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let mut ctors = tree_forest_ctors(&p, ids[0], ids[1]);
    ctors.push((ids[1], vec![]));
    assert_eq!(code(define_data_group(&mut p.g, ctors)), "E-MALFORMED");
    assert_eq!(state(&p.g, ids[0]), State::Failed);

    // A type that wasn't declared in the group can't be added to it.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let extra = data(&mut p.g, "Extra", vec![], Sort::Type(0));
    let mut ctors = tree_forest_ctors(&p, ids[0], ids[1]);
    ctors.push((
        extra,
        vec![ctor("MkExtra", vec![("t", Term::Data(ids[0], vec![]))])],
    ));
    assert_eq!(code(define_data_group(&mut p.g, ctors)), "E-MALFORMED");
    assert_eq!(&*p.g.data(ids[0]).group, &ids[..]);
    assert_eq!(&*p.g.data(extra).group, &[extra]);
    for d in [ids[0], ids[1], extra] {
        assert_eq!(state(&p.g, d), State::Failed);
    }

    // A final group can't be defined again.
    let mut p = Prelude::new();
    let (tree, forest) = tree_forest(&mut p);
    let ctors = tree_forest_ctors(&p, tree, forest);
    assert_eq!(code(define_data_group(&mut p.g, ctors)), "E-MALFORMED");
    assert_eq!(state(&p.g, tree), State::Final);

    // Neighbour: every member, in any order.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let mut ctors = tree_forest_ctors(&p, ids[0], ids[1]);
    ctors.reverse();
    assert_eq!(code(define_data_group(&mut p.g, ctors)), "ok");

    // An empty group, and an unknown type: refused, and nothing changes.
    let mut p = Prelude::new();
    assert_eq!(
        code(try_group(&mut p.g, &[], vec![], Sort::Type(0))),
        "E-MALFORMED"
    );
    assert_eq!(code(define_data_group(&mut p.g, vec![])), "E-MALFORMED");
    let unknown = DataId(p.g.datas.len());
    assert_eq!(
        code(define_data_group(&mut p.g, vec![(unknown, vec![])])),
        "E-MALFORMED"
    );
}

#[test]
fn a_header_cannot_mention_a_member_or_anything_unknown() {
    // The parameters mention the id the first member would get, or one
    // further on, or a definition that doesn't exist: refused before
    // anything is added.
    let mut p = Prelude::new();
    let (datas, defs) = (p.g.datas.len(), p.g.defs.len());
    for forged in [
        Term::Data(DataId(datas), vec![]),
        Term::Data(DataId(datas + 1), vec![]),
        Term::Def(DefId(defs)),
    ] {
        let r = try_group(&mut p.g, &["A", "B"], vec![("x", forged)], Sort::Type(0));
        assert_eq!(code(r), "E-MALFORMED");
        assert_eq!((p.g.datas.len(), p.g.defs.len()), (datas, defs));
    }
    // A pending data type, or definition.
    let pending = data(&mut p.g, "Pending", vec![], Sort::Type(0));
    let r = try_group(
        &mut p.g,
        &["A", "B"],
        vec![("x", Term::Data(pending, vec![]))],
        Sort::Type(0),
    );
    assert_eq!(code(r), "E-MALFORMED");
    let f = declare(&mut p.g, "f", ty());
    let r = try_group(
        &mut p.g,
        &["A", "B"],
        vec![("x", Term::Def(f))],
        Sort::Type(0),
    );
    assert_eq!(code(r), "E-MALFORMED");
    assert_eq!(p.g.datas.len(), datas + 1);
    // Neighbour: a final one, and an earlier parameter.
    let r = try_group(
        &mut p.g,
        &["A", "B"],
        vec![("a", ty()), ("xs", Term::data(p.list, vec![v(0)]))],
        Sort::Type(0),
    );
    let ids = r.unwrap();
    assert_eq!(p.g.data(ids[0]).params.len(), 2);
    assert_eq!(p.g.data(ids[1]).params.len(), 2);
}

#[test]
fn a_field_can_mention_a_sibling_type_but_not_its_constructors() {
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Tree", "Forest"], vec![], Sort::Type(0));
    let (tree, forest) = (ids[0], ids[1]);
    // Tree = Node (kids : Forest) (ok : kids = FNil)
    let fnil = Term::ctor(forest, 0, vec![]);
    let fields = vec![
        (
            tree,
            vec![ctor(
                "Node",
                vec![
                    ("kids", Term::Data(forest, vec![])),
                    ("ok", eq(None, v(0), fnil)),
                ],
            )],
        ),
        tree_forest_ctors(&p, tree, forest).pop().unwrap(),
    ];
    let e = define_data_group(&mut p.g, fields).unwrap_err();
    assert_eq!(e.code, "E-MALFORMED");
    assert!(
        e.labels[0].message.contains("`Forest`'s constructors"),
        "{:?}",
        e.labels
    );
    assert_eq!(state(&p.g, tree), State::Failed);
    assert_eq!(state(&p.g, forest), State::Failed);

    // Nor a pending definition, nor a data type declared after the group.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["A", "B"], vec![], Sort::Type(0));
    let later = data(&mut p.g, "Later", vec![], Sort::Type(0));
    check::define_ctors(&mut p.g, later, vec![ctor("L", vec![])]).unwrap();
    let fields = vec![
        (
            ids[0],
            vec![ctor("MkA", vec![("x", Term::Data(later, vec![]))])],
        ),
        (
            ids[1],
            vec![ctor("MkB", vec![("y", Term::Data(ids[0], vec![]))])],
        ),
    ];
    let r = define_data_group(&mut p.g, fields);
    assert_eq!(code(r), "E-POSITIVITY");
    let mut p = Prelude::new();
    let ids2 = group(&mut p.g, &["A", "B"], vec![], Sort::Type(0));
    let f = declare(&mut p.g, "f", ty());
    let r = define_data_group(
        &mut p.g,
        vec![
            (ids2[0], vec![ctor("MkA", vec![("x", Term::Def(f))])]),
            (ids2[1], vec![]),
        ],
    );
    assert_eq!(code(r), "E-MALFORMED");
    // Neighbour: a sibling declared after it in the group is fine (it's
    // the group's), as is a final type declared before the group.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["A", "B"], vec![], Sort::Type(0));
    let nat = p.nat_ty();
    let r = define_data_group(
        &mut p.g,
        vec![
            (
                ids[0],
                vec![ctor(
                    "MkA",
                    vec![("b", Term::Data(ids[1], vec![])), ("n", nat)],
                )],
            ),
            (
                ids[1],
                vec![
                    ctor("End", vec![]),
                    ctor("MkB", vec![("a", Term::Data(ids[0], vec![]))]),
                ],
            ),
        ],
    );
    assert_eq!(code(r), "ok");
}

#[test]
fn a_failed_dependency_fails_every_member() {
    let mut p = Prelude::new();
    let f = declare(&mut p.g, "f", ty());
    let nat = p.nat_ty();
    assert_eq!(code(check::define_def(&mut p.g, f, &nat)), "ok");
    let bad = declare(&mut p.g, "bad", ty());
    let zero = p.num(0);
    assert_eq!(
        code(check::define_def(&mut p.g, bad, &zero)),
        "E-TYPE-MISMATCH"
    );
    let ids = group(&mut p.g, &["A", "B"], vec![], Sort::Type(0));
    let r = define_data_group(
        &mut p.g,
        vec![
            (
                ids[0],
                vec![ctor("MkA", vec![("b", Term::Data(ids[1], vec![]))])],
            ),
            (
                ids[1],
                vec![
                    ctor("End", vec![]),
                    ctor("MkB", vec![("x", Term::Def(bad))]),
                ],
            ),
        ],
    );
    assert_eq!(code(r), "E-FAILED-DEPENDENCY");
    for d in ids {
        assert_eq!(state(&p.g, d), State::Failed);
        assert_eq!(data_hash(&p.g, d).unwrap(), None);
    }
}

#[test]
fn members_share_one_universe() {
    // A field in `Type 0` is too large for a group in `Prop`... and `Type` is
    // too large for a group in `Type 0`.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["A", "B"], vec![], Sort::Type(0));
    let r = define_data_group(
        &mut p.g,
        vec![
            (
                ids[0],
                vec![ctor("MkA", vec![("b", Term::Data(ids[1], vec![]))])],
            ),
            (
                ids[1],
                vec![ctor("End", vec![]), ctor("MkB", vec![("t", ty())])],
            ),
        ],
    );
    assert_eq!(code(r), "E-UNIVERSE");
    assert_eq!(state(&p.g, ids[0]), State::Failed);
    // Neighbour: the same in `Type 1`.
    let ids = group(&mut p.g, &["A", "B"], vec![], Sort::Type(1));
    let r = define_data_group(
        &mut p.g,
        vec![
            (
                ids[0],
                vec![ctor("MkA", vec![("b", Term::Data(ids[1], vec![]))])],
            ),
            (
                ids[1],
                vec![ctor("End", vec![]), ctor("MkB", vec![("t", ty())])],
            ),
        ],
    );
    assert_eq!(code(r), "ok");
    assert_eq!(p.g.data(ids[1]).sort, Sort::Type(1));
}

/// `EvenP = EvenZero | EvenSucc (o : OddP)`, `OddP = OddSucc (e : EvenP)`,
/// in `Prop`: as a group, or (for `OddP`'s neighbour) `OddP` on its own,
/// about a final `EvenP`.
fn even_odd_props(p: &mut Prelude, together: bool) -> (DataId, DataId) {
    if together {
        let ids = group(&mut p.g, &["EvenP", "OddP"], vec![], Sort::Prop);
        let (even, odd) = (ids[0], ids[1]);
        let r = define_data_group(
            &mut p.g,
            vec![
                (
                    even,
                    vec![
                        ctor("EvenZero", vec![]),
                        ctor("EvenSucc", vec![("o", Term::Data(odd, vec![]))]),
                    ],
                ),
                (
                    odd,
                    vec![ctor("OddSucc", vec![("e", Term::Data(even, vec![]))])],
                ),
            ],
        );
        r.unwrap();
        (even, odd)
    } else {
        let even = data(&mut p.g, "EvenP", vec![], Sort::Prop);
        check::define_ctors(&mut p.g, even, vec![ctor("EvenZero", vec![])]).unwrap();
        let odd = data(&mut p.g, "OddP", vec![], Sort::Prop);
        let fields = vec![ctor("OddSucc", vec![("e", Term::Data(even, vec![]))])];
        check::define_ctors(&mut p.g, odd, fields).unwrap();
        (even, odd)
    }
}

#[test]
fn propositions_defined_together_eliminate_only_into_propositions() {
    // oddDepth (OddSucc e) = 1: `OddP` has one constructor, whose only field
    // is a proof, which on its own could be matched to produce data.
    let depth = |p: &mut Prelude, odd: DataId| {
        let ty = arrow(Term::Data(odd, vec![]), p.nat_ty());
        let body = lam("o", case(0, odd, vec![(vec!["e"], p.num(1))]));
        define(&mut p.g, "oddDepth", ty, body).err()
    };
    let mut p = Prelude::new();
    let (_, odd) = even_odd_props(&mut p, true);
    assert_eq!(depth(&mut p, odd), Some("E-PROP-ELIM"));
    // Neighbour: on its own, it can.
    let mut p = Prelude::new();
    let (_, odd) = even_odd_props(&mut p, false);
    assert_eq!(depth(&mut p, odd), None);
    // Neighbour: matching on a proof in the group to produce another proof,
    // by mutual recursion over the proofs: oddToEven (OddSucc e) = EvenSucc
    // (OddSucc e), and EvenP -> Unit and OddP -> Unit calling each other.
    let mut p = Prelude::new();
    let (even, odd) = even_odd_props(&mut p, true);
    let unit = data(&mut p.g, "Unit", vec![], Sort::Prop);
    check::define_ctors(&mut p.g, unit, vec![ctor("Trivial", vec![])]).unwrap();
    let to_unit = |d: DataId| arrow(Term::Data(d, vec![]), Term::Data(unit, vec![]));
    let fe = check::declare_def(
        &mut p.g,
        &"evenTrivial".into(),
        &to_unit(even),
        true,
        false,
        span(),
    );
    let fo = check::declare_def(
        &mut p.g,
        &"oddTrivial".into(),
        &to_unit(odd),
        true,
        false,
        span(),
    );
    let (fe, fo) = (fe.unwrap(), fo.unwrap());
    let trivial = Term::ctor(unit, 0, vec![]);
    let bodies = vec![
        (
            fe,
            lam(
                "e",
                case(
                    0,
                    even,
                    vec![(vec![], trivial), (vec!["o"], app(Term::Def(fo), [v(0)]))],
                ),
            ),
        ),
        (
            fo,
            lam(
                "o",
                case(0, odd, vec![(vec!["e"], app(Term::Def(fe), [v(0)]))]),
            ),
        ),
    ];
    assert_eq!(code(check::define_group(&mut p.g, &bodies)), "ok");
}

#[test]
fn a_function_field_returning_a_sibling_gives_smaller_values() {
    // Branching = Tip | Fork (w : Nat) (child : Nat -> Layer),
    // Layer = MkLayer (below : Branching);
    // depth Tip n = 0; depth (Fork w child) n = layerDepth (child n) n;
    // layerDepth (MkLayer b) n = depth b n.
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &["Branching", "Layer"], vec![], Sort::Type(0));
    let (branching, layer) = (ids[0], ids[1]);
    let child_ty = arrow(p.nat_ty(), Term::Data(layer, vec![]));
    let nat_ty = p.nat_ty();
    define_data_group(
        &mut p.g,
        vec![
            (
                branching,
                vec![
                    ctor("Tip", vec![]),
                    ctor("Fork", vec![("w", nat_ty), ("child", child_ty)]),
                ],
            ),
            (
                layer,
                vec![ctor(
                    "MkLayer",
                    vec![("below", Term::Data(branching, vec![]))],
                )],
            ),
        ],
    )
    .unwrap();
    let nat = p.nat_ty();
    let ty = |d: DataId| arrow(Term::Data(d, vec![]), arrow(nat.clone(), nat.clone()));
    let depth = declare(&mut p.g, "depth", ty(branching));
    let layer_depth = declare(&mut p.g, "layerDepth", ty(layer));
    let call_child = app(Term::Def(layer_depth), [app(v(0), [v(2)]), v(2)]);
    let bodies = vec![
        (
            depth,
            lam(
                "b",
                lam(
                    "n",
                    case(
                        1,
                        branching,
                        vec![(vec![], p.num(0)), (vec!["w", "child"], call_child)],
                    ),
                ),
            ),
        ),
        (
            layer_depth,
            lam(
                "l",
                lam(
                    "n",
                    case(
                        1,
                        layer,
                        vec![(vec!["b"], app(Term::Def(depth), [v(0), v(1)]))],
                    ),
                ),
            ),
        ),
    ];
    assert_eq!(code(check::define_group(&mut p.g, &bodies)), "ok");
}

/// Hashes of a final `Tree`/`Forest` group, declared in the given order,
/// with `FCons`'s fields given by `fcons` (in terms of `Tree` and `Forest`),
/// and `Forest`'s constructors named `names`.
fn tree_forest_hashes(
    order: [&str; 2],
    names: [&str; 2],
    fcons: impl Fn(Term, Term) -> Vec<(&'static str, Term)>,
    sort: Sort,
) -> (ContentHash, ContentHash) {
    let mut p = Prelude::new();
    let ids = group(&mut p.g, &order, vec![], sort);
    let (tree, forest) = if order[0] == "Tree" {
        (ids[0], ids[1])
    } else {
        (ids[1], ids[0])
    };
    let (t, f) = (Term::Data(tree, vec![]), Term::Data(forest, vec![]));
    let ctors = vec![
        (
            tree,
            vec![ctor(
                "Node",
                vec![("label", p.nat_ty()), ("kids", f.clone())],
            )],
        ),
        (
            forest,
            vec![ctor(names[0], vec![]), ctor(names[1], fcons(t, f))],
        ),
    ];
    define_data_group(&mut p.g, ctors).unwrap();
    let hash = |d| data_hash(&p.g, d).unwrap().expect("final");
    (hash(tree), hash(forest))
}

#[test]
fn a_data_group_is_hashed_as_a_unit() {
    let usual = |t: Term, f: Term| vec![("first", t), ("rest", f)];
    let base = tree_forest_hashes(["Tree", "Forest"], ["FNil", "FCons"], usual, Sort::Type(0));
    assert_eq!(
        base,
        tree_forest_hashes(["Tree", "Forest"], ["FNil", "FCons"], usual, Sort::Type(0)),
        "deterministic"
    );
    assert_ne!(base.0, base.1, "each member has its own hash");
    // Declared in the other order: the same hashes (ordered by name).
    assert_eq!(
        base,
        tree_forest_hashes(["Forest", "Tree"], ["FNil", "FCons"], usual, Sort::Type(0)),
    );
    // Changing one constructor of one member changes every member's hash.
    let swapped = |t: Term, f: Term| vec![("rest", f), ("first", t)];
    let changed = tree_forest_hashes(
        ["Tree", "Forest"],
        ["FNil", "FCons"],
        swapped,
        Sort::Type(0),
    );
    assert_ne!(base.0, changed.0);
    assert_ne!(base.1, changed.1);
    // So does renaming one constructor.
    let renamed = tree_forest_hashes(["Tree", "Forest"], ["Empty", "FCons"], usual, Sort::Type(0));
    assert_ne!(base.0, renamed.0);
    // And the universe, which is the group's.
    let larger = tree_forest_hashes(["Tree", "Forest"], ["FNil", "FCons"], usual, Sort::Type(1));
    assert_ne!(base.0, larger.0);
    assert_ne!(base.1, larger.1);
    // A reference to one member is different from one to the other: a
    // forest of forests.
    let other = |_: Term, f: Term| vec![("first", f.clone()), ("rest", f)];
    let other = tree_forest_hashes(["Tree", "Forest"], ["FNil", "FCons"], other, Sort::Type(0));
    assert_ne!(base.0, other.0);
}

#[test]
fn definitions_over_a_data_group_hash_its_members_and_constructors() {
    // first : Forest -> Tree ... a reference to each constructor of a
    // member is different.
    let hash_of = |c: usize| {
        let mut p = Prelude::new();
        let (tree, forest) = tree_forest(&mut p);
        let ty = arrow(Term::Data(tree, vec![]), Term::Data(forest, vec![]));
        let body = match c {
            0 => lam("t", Term::ctor(forest, 0, vec![])),
            _ => lam(
                "t",
                Term::ctor(forest, 1, vec![v(0), Term::ctor(forest, 0, vec![])]),
            ),
        };
        let id = define(&mut p.g, "f", ty, body).unwrap();
        def_hash(&p.g, id).unwrap().expect("final")
    };
    assert_ne!(hash_of(0), hash_of(1));
    assert_eq!(hash_of(1), hash_of(1));
}

#[test]
fn members_with_the_same_name_hash_deterministically() {
    // The kernel doesn't require distinct names: ties are broken by
    // declaration order.
    let hashes = || {
        let mut p = Prelude::new();
        let ids = group(&mut p.g, &["T", "T"], vec![], Sort::Type(0));
        let ctors = vec![
            (
                ids[0],
                vec![ctor("A", vec![("x", Term::Data(ids[1], vec![]))])],
            ),
            (
                ids[1],
                vec![
                    ctor("B", vec![]),
                    ctor("C", vec![("y", Term::Data(ids[0], vec![]))]),
                ],
            ),
        ];
        define_data_group(&mut p.g, ctors).unwrap();
        (
            data_hash(&p.g, ids[0]).unwrap().unwrap(),
            data_hash(&p.g, ids[1]).unwrap().unwrap(),
        )
    };
    let (a, b) = hashes();
    assert_eq!((a, b), hashes());
    assert_ne!(a, b);
}

use super::*;

#[test]
fn indexed_families_have_indices_result_types_and_implicit_fields() {
    let module = parse(
        "type Sub (a: Type): (n: Nat) -> Fin n -> Type =\n  \
         | Here [m: Nat] (x: a): Sub a (Succ m) FZero\n  | There\n\n\
         def f: Vec a n -> Nat\n  | VCons [n := k] _ _ => k\n",
    );
    let Decl::Data {
        indices,
        sort,
        ctors,
        ..
    } = &module.decls[0]
    else {
        panic!("expected a data type");
    };
    let names: Vec<Option<&str>> = indices
        .iter()
        .map(|(n, _)| n.as_ref().map(|n| n.text.as_str()))
        .collect();
    assert_eq!(names, [Some("n"), None]);
    assert!(matches!(sort, Some(Expr::Type(0, _))));
    assert_eq!(ctors[0].implicit, [true, false]);
    assert!(ctors[0].result.is_some());
    assert!(ctors[1].result.is_none() && ctors[1].fields.is_empty());
    let Decl::Equation { patterns, .. } = &module.decls[2] else {
        panic!("expected an arm");
    };
    let Pattern::Ctor(_, args, _) = &patterns[0] else {
        panic!("expected a constructor pattern");
    };
    assert!(matches!(&args[0], Pattern::Named(n, p, _)
        if n.text == "n" && matches!(**p, Pattern::Var(_))));
    // A synonym has no indices.
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", "");
    assert!(parse_module(file, "type T: Nat -> Type = Nat\n").is_err());
}

#[test]
fn a_record_declaration_is_one_constructor() {
    let module = parse("type Person =\n  { name : Text\n  , age : Nat\n  }\n\ntype Empty = {}\n");
    let Decl::Data {
        ctors,
        record: true,
        ..
    } = &module.decls[0]
    else {
        panic!("expected a record");
    };
    assert_eq!(ctors.len(), 1);
    assert_eq!(ctors[0].name.text, "%mk");
    let names: Vec<&str> = ctors[0]
        .fields
        .iter()
        .map(|b| b.names[0].text.as_str())
        .collect();
    assert_eq!(names, ["name", "age"]);
    assert!(
        matches!(&module.decls[1], Decl::Data { ctors, record: true, .. } if ctors[0].fields.is_empty())
    );
}

#[test]
fn a_constructor_declared_with_its_fields_in_braces() {
    let module = parse(
        "type Event =\n  | Meeting { title : Text, minutes : Nat := 30 }\n  | Reminder (title : Text)\n  | Node [n : Nat] { x : Nat }\n",
    );
    let Decl::Data { ctors, .. } = &module.decls[0] else {
        panic!("expected a data declaration");
    };
    assert!(ctors[0].braced && !ctors[1].braced);
    assert_eq!(ctors[0].fields.len(), 2);
    assert_eq!(ctors[0].defaults.len(), 2);
    assert_eq!(ctors[2].implicit, [true, false]);
    let e = parse_error("type T =\n  | C (a : Nat) { b : Nat }\n");
    assert!(e.message.contains("fields in brackets already"), "{e:?}");
}

#[test]
fn indented_lines_continue_a_declaration() {
    let module = parse(
        "type List (a : Type) : Type =\n  | Nil\n  | Cons (head : a) (tail : List a)\n\ndef length (a : Type) : List a -> Nat\n  | Nil => 0\n",
    );
    assert_eq!(module.decls.len(), 3);
    let Decl::Data { ctors, .. } = &module.decls[0] else {
        panic!("expected a data declaration");
    };
    assert_eq!(ctors.len(), 2);
}

#[test]
fn export_attaches_to_the_definition_it_precedes() {
    let module = parse("export def f (n : Nat) : Nat := n\n");
    assert_eq!(module.decls.len(), 2);
    assert!(matches!(
        module.decls[0],
        Decl::Signature { export: true, .. }
    ));
}

#[test]
fn parses_tests() {
    let module = parse("test \"two \\\"words\\\"\" :=\n  1 + 1 = 2\n");
    let Decl::Test { name, expr, .. } = &module.decls[0] else {
        panic!("expected a test");
    };
    assert_eq!(name, "two \"words\"");
    assert!(matches!(expr, Expr::Binary(BinOp::Eq, ..)));
}

#[test]
fn parses_both_kinds_of_if() {
    assert!(matches!(
        expr("if b then 1 else 2"),
        Expr::If { binder: None, .. }
    ));
    assert!(matches!(
        expr("if h : d != 0 then n / d else 0"),
        Expr::If {
            binder: Some(_),
            ..
        }
    ));
}

#[test]
fn parses_auto_binders_and_absurd_patterns() {
    let module = parse(
        "def div : (n d : Nat) -> [auto ok : d != 0] -> Nat\ndef absurd : Void -> a\n  | ()\n",
    );
    let Decl::Signature { ty, .. } = &module.decls[0] else {
        panic!("expected a signature");
    };
    let Expr::Pi { cod, .. } = ty else {
        panic!("expected a function type");
    };
    assert!(
        matches!(cod.as_ref(), Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == "ok")
    );
    let Decl::Equation { patterns, rhs, .. } = &module.decls[2] else {
        panic!("expected an equation");
    };
    assert!(matches!(patterns[..], [Pattern::Absurd(_)]));
    assert!(rhs.is_none());
    // `auto` alone is an ordinary name.
    let module = parse("def f : [auto : Type] -> auto\n");
    let Decl::Signature { ty, .. } = &module.decls[0] else {
        panic!("expected a signature");
    };
    assert!(matches!(ty, Expr::Pi { auto: false, .. }));
}

#[test]
fn parses_interfaces_instances_and_auto_binders_without_names() {
    let module = parse(
        "interface Pretty (a: Type) = { pretty: a -> Text }\n\
         instance List.instPretty [auto Pretty a]: Pretty (List a) := { pretty = xs => \"\" }\n\
         def f: [auto Pretty a] -> a -> Text := x => Pretty.pretty x\n\
         def g: List [auto] -> Nat := 0\n",
    );
    assert!(matches!(
        &module.decls[0],
        Decl::Data { record: true, interface: true, ctors, .. } if ctors[0].fields.len() == 1
    ));
    let Decl::Signature { ty, instance, .. } = &module.decls[1] else {
        panic!("expected a signature");
    };
    assert!(*instance);
    assert!(matches!(
        ty,
        Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == crate::ast::NAMELESS
    ));
    let Decl::Signature { ty, instance, .. } = &module.decls[3] else {
        panic!("expected a signature");
    };
    assert!(!*instance);
    assert!(matches!(
        ty,
        Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == crate::ast::NAMELESS
    ));
    // `[auto]` is still a list.
    let Decl::Signature { ty, .. } = &module.decls[5] else {
        panic!("expected a signature");
    };
    assert!(matches!(ty, Expr::Arrow(..)));
    // An instance needs a body.
    let mut sources = SourceMap::new();
    let text = "interface I (a: Type) = { x: a }\ninstance n: I Nat\n";
    let file = sources.add("test.sw", text);
    assert!(parse_module(file, text).is_err());
}

#[test]
fn parses_auto_parameters_of_types() {
    // docs/proposals/interfaces.md §7.5.
    let module = parse(
        "type Map (k: Type) (v: Type) [auto ord: Ord k] = { entries: List (k, v) }\n\
         type Tree (k: Type) [auto ord: Ord k] = | Leaf | Node (l: Tree k)\n\
         type Set (k: Type) [auto ord: Ord k] = Map k () [ord := ord]\n",
    );
    assert!(matches!(
        &module.decls[0],
        Decl::Data { record: true, params, auto_params, .. }
            if params.len() == 3 && auto_params == &[false, false, true]
    ));
    assert!(matches!(
        &module.decls[1],
        Decl::Data { record: false, auto_params, .. } if auto_params == &[false, true]
    ));
    // A synonym's is the definition's.
    let Decl::Signature {
        ty, synonym: true, ..
    } = &module.decls[2]
    else {
        panic!("expected a synonym");
    };
    let Expr::Pi { cod, .. } = ty else {
        panic!("expected a function type, got {ty:?}");
    };
    assert!(matches!(
        &**cod,
        Expr::Pi { implicit: true, auto: true, names, .. } if names[0].text == "ord"
    ));
    let d = parse_error("type T [a: Type] = { x: a }\n");
    assert!(d.message.contains("must be `auto`"), "{}", d.message);
    let d = parse_error("type T (a: Type) [auto Ord a] = { x: a }\n");
    assert!(d.message.contains("needs a name"), "{}", d.message);
}

#[test]
fn decreasing_goes_after_the_result_type() {
    // `:=` may start a line at the declaration's column after it.
    for source in [
        "def f (n: Nat): Nat\n  decreasing n\n:=\n  f (n / 2) [decreasing := p]\n",
        "def f (n: Nat): Nat decreasing n := f (n / 2) [decreasing := p]\n",
        "def f (n: Nat): Nat -> Nat\n  decreasing n\n  | Zero => 0\n  | Succ k => k\n",
    ] {
        let module = parse(source);
        assert!(
            matches!(
                &module.decls[0],
                Decl::Signature {
                    decreasing: Some(_),
                    ..
                }
            ),
            "{source}"
        );
        assert!(module.decls.len() >= 2, "{source}");
    }
    let module = parse("def f (n: Nat): Nat decreasing n := f (n / 2) [decreasing := p]\n");
    let Decl::Equation { rhs: Some(rhs), .. } = &module.decls[1] else {
        panic!("expected the body");
    };
    let Expr::App(_, arg) = rhs else {
        panic!("expected a call, got {rhs:?}");
    };
    assert!(matches!(&**arg, Expr::NamedArg(n, ..) if n.text == "decreasing"));
}

/// `opaque def`, and `unfolding` after the result type and after
/// `decreasing` (docs/proposals/opaque-definitions.md §6.2, §6.3).
#[test]
fn opaque_and_unfolding() {
    for (source, export, names) in [
        ("opaque def f (n: Nat): Nat := n\n", false, vec![]),
        ("export opaque def f (n: Nat): Nat := n\n", true, vec![]),
        (
            "opaque def f (n: Nat): Nat unfolding g, Code := n\n",
            false,
            vec!["g", "Code"],
        ),
        (
            "opaque def f (n: Nat): Nat\n    decreasing n\n    unfolding A.g\n:=\n  n\n",
            false,
            vec!["A.g"],
        ),
        (
            "opaque def f: Nat -> Nat\n    unfolding g\n  | Zero => 0\n  | Succ k => k\n",
            false,
            vec!["g"],
        ),
    ] {
        let module = parse(source);
        let Decl::Signature {
            opaque: true,
            export: e,
            unfolding,
            ..
        } = &module.decls[0]
        else {
            panic!("not an opaque signature: {source}");
        };
        assert_eq!(*e, export, "{source}");
        let found: Vec<&str> = unfolding.iter().map(|n| n.text.as_str()).collect();
        assert_eq!(found, names, "{source}");
        assert!(module.decls.len() >= 2, "{source}");
    }
    let module = parse("theorem t: f 1 = 1\n    unfolding f\n  := rfl\n");
    assert!(matches!(
        &module.decls[0],
        Decl::Signature { theorem: true, opaque: false, unfolding, .. } if unfolding.len() == 1
    ));
    // A type that starts on its own line is a block; the clause on a line
    // at the block's column still ends it.
    for source in [
        "theorem t:\n  f 1 = 1\n  unfolding f\n  := rfl\n",
        "opaque def g (n: Nat):\n  Nat\n  decreasing n\n  unfolding f\n  := n\n",
    ] {
        let module = parse(source);
        assert!(
            matches!(&module.decls[0], Decl::Signature { unfolding, .. } if unfolding.len() == 1),
            "{source}"
        );
    }
    for (source, message) in [
        (
            "opaque theorem t: 1 = 1 := rfl\n",
            "a theorem can't be `opaque`",
        ),
        (
            "opaque instance i: Show Nat := s\n",
            "an instance can't be `opaque`",
        ),
        (
            "opaque export def f: Nat := 1\n",
            "`export` goes before `opaque`",
        ),
        (
            "instance i: Show Nat unfolding f := s\n",
            "an instance can't have `unfolding`",
        ),
        (
            "def f (n: Nat): Nat unfolding g decreasing n := n\n",
            "`decreasing` goes before `unfolding`",
        ),
        (
            "def f (n: Nat): Nat :=\n  def g (m: Nat): Nat unfolding h := m\n  g n\n",
            "a local definition can't have `unfolding`",
        ),
        (
            "def f (n: Nat): Nat :=\n  opaque def g (m: Nat): Nat := m\n  g n\n",
            "local definitions can't be `opaque`: only top-level ones can",
        ),
    ] {
        assert_eq!(parse_error(source).message, message, "{source}");
    }
}

#[test]
fn a_theorem_may_say_forall_before_its_parameters() {
    // D3472: cosmetic, so the same tree as without it.
    let with = parse("theorem t ∀ (n: Nat) (h: n < 1): n = 0 := rfl\n");
    let without = parse("theorem t (n: Nat) (h: n < 1): n = 0 := rfl\n");
    assert_eq!(
        crate::equivalence::shape(&with),
        crate::equivalence::shape(&without)
    );
    let ascii = parse("theorem t forall [a: Type] (n: Nat): n = n := rfl\n");
    assert_eq!(ascii.decls.len(), 2);
}

#[test]
fn forall_before_the_parameters_is_for_theorems_with_a_parameter() {
    let message = parse_error("def f ∀ (n: Nat): Nat := n\n").message;
    assert!(message.contains("only for theorems"), "{message}");
    let message = parse_error("theorem t ∀: True := trivial\n").message;
    assert!(message.contains("after `∀`"), "{message}");
}

#[test]
fn a_theorem_statement_compares_the_pipeline() {
    for (source, want) in [
        ("theorem t: xs |> .length = n := rfl\n", "(Eq xs.length n)"),
        (
            "theorem t: xs |> List.length = n := rfl\n",
            "(Eq (|> xs List.length) n)",
        ),
        (
            "theorem t:\n  xs\n    |> .map f\n    |> .length = n\n  := rfl\n",
            "(Eq (xs.map f).length n)",
        ),
    ] {
        let module = parse(source);
        let Decl::Signature { ty, .. } = &module.decls[0] else {
            panic!("expected a theorem: {source}");
        };
        assert_eq!(pshape(ty), want, "{source}");
    }
}

#[test]
fn a_namespace_line_is_read_with_its_path() {
    let module = parse("-- a file\nnamespace Day05\n\nimport List (map)\n\ndef x: Nat := 1\n");
    assert_eq!(module.namespace.unwrap().path.text, "Day05");
    assert_eq!(module.imports.len(), 1);
    assert!(!module.decls.is_empty());
    let module = parse("namespace Aoc.Day05\ndef x: Nat := 1\n");
    assert_eq!(module.namespace.unwrap().path.text, "Aoc.Day05");
    assert!(parse("def x: Nat := 1\n").namespace.is_none());
}

#[test]
fn import_items_may_be_renamed() {
    let module = parse("import List (map as each, length, Tree as T)\n");
    let items = &module.imports[0].items;
    let read: Vec<(&str, Option<&str>, &str)> = items
        .iter()
        .map(|i| {
            (
                i.name.text.as_str(),
                i.alias.as_ref().map(|a| a.text.as_str()),
                i.local().text.as_str(),
            )
        })
        .collect();
    assert_eq!(
        read,
        [
            ("map", Some("each"), "each"),
            ("length", None, "length"),
            ("Tree", Some("T"), "T")
        ]
    );
    // The alias keeps the name's kind; `import M as A` says what to write.
    let e = parse_error("import List (map as Each)\n");
    assert!(e.message.contains("so its new name must too"), "{e:?}");
    let e = parse_error("import Shop.Spec as S\n");
    assert!(
        e.notes
            .iter()
            .any(|n| n.contains("import Shop (Spec as S)")),
        "{e:?}"
    );
    let e = parse_error("import List (map as)\n");
    assert_eq!(e.code, "E-PARSE");
}

#[test]
fn import_everything_is_read_with_its_dots() {
    let module = parse("import List (..)\n\ndef x: Nat := 1\n");
    let import = &module.imports[0];
    assert_eq!(import.path.text, "List");
    assert!(import.items.is_empty());
    let dots = import.everything.expect("`(..)`");
    assert_eq!((dots.start, dots.end), (13, 15));
    let module = parse("import Std.List (..)\n");
    assert_eq!(module.imports[0].path.text, "Std.List");
    assert!(module.imports[0].everything.is_some());
    let module = parse("import List (map)\n");
    assert!(module.imports[0].everything.is_none());
    for source in ["import Aoc (Range, ..)\n", "import Aoc (.., Range)\n"] {
        let e = parse_error(source);
        assert!(
            e.message
                .contains("so it goes on its own: `import Aoc (..)`"),
            "{e:?}"
        );
    }
    let e = parse_error("import List ()\n");
    assert!(e.message.contains("a name to import"), "{e:?}");
    let e = parse_error("import List\n");
    assert!(e.message.contains("`(` and the names to import"), "{e:?}");
}

#[test]
fn a_namespace_line_has_to_be_well_formed_and_first() {
    let e = parse_error("namespace Demo.day\n");
    assert!(e.message.contains("starts with a capital letter"), "{e:?}");
    let e = parse_error("namespace demo.Day\n");
    assert!(e.message.contains("starts with a capital letter"), "{e:?}");
    let e = parse_error("namespace\n");
    assert!(e.message.contains("a namespace, such as `Day05`"), "{e:?}");
    let e = parse_error("namespace 5\n");
    assert!(e.message.contains("a namespace, such as `Day05`"), "{e:?}");
    let e = parse_error("namespace A\nnamespace B\n");
    assert!(e.message.contains("only one namespace line"), "{e:?}");
    assert!(e.notes[0].contains("import from it"), "{e:?}");
    let e = parse_error("import List (map)\nnamespace A\n");
    assert_eq!(e.code, "E-NAMESPACE-NOT-FIRST", "{e:?}");
    assert!(e.message.contains("must come first"), "{e:?}");
    assert!(
        e.notes[0].contains("move `namespace A` to the top"),
        "{e:?}"
    );
    let e = parse_error("def x: Nat := 1\nnamespace A\n");
    assert!(e.message.contains("must come first"), "{e:?}");
}

#[test]
fn namespace_is_a_keyword() {
    assert!(parse_module_text("def namespace: Nat := 1\n").is_err());
}

#[test]
fn recovery_keeps_good_declarations_and_names_the_broken() {
    let text = "def a: Nat := 1\n\ndef b (n: Nat): Nat := n +\n\n\
                type T\n  | MkT (x: Nat\n\ndef c: Nat := (\n\ndef d: Nat := 2\n";
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
    assert_eq!(errors.len(), 3);
    let kept: Vec<&str> = module
        .decls
        .iter()
        .filter_map(|d| match d {
            Decl::Signature { name, .. } => Some(name.text.as_str()),
            _ => None,
        })
        .collect();
    // `b` and `c` keep their headers (`recovery_keeps_the_header_of_a_body_that_does_not_parse`).
    assert_eq!(kept, ["a", "b", "c", "d"]);
    let failed: Vec<&str> = module.failed.iter().map(|n| n.name.text.as_str()).collect();
    assert_eq!(failed, ["T", "MkT"]);
}

/// A `def` or `theorem` whose header parses and whose body doesn't is
/// kept, with the place of its first error and one equation whose body
/// is (or holds) a missing expression, so its signature can stand in
/// for its statement
/// (docs/proposals/tests-with-errors.md §3.3). One whose header doesn't
/// parse, and an instance, are left out as before.
#[test]
fn recovery_keeps_the_header_of_a_body_that_does_not_parse() {
    let text = "def double (n: Nat): Nat := n + n\n\n\
                @[simp] theorem doubleTwo: double 2 = 4 := (rfl\n\n\
                export def arms: Nat -> Nat\n  | 0 => 1\n  | n => (n\n\n\
                def trailing: Nat := 1 )\n\n\
                def local: Nat :=\n  def inner: Nat := 1\n  inner +\n\n\
                theorem header: double 2 = := rfl\n\n\
                instance inst: Inhabited Nat := (0\n\n\
                def last: Nat := 2\n";
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
    assert_eq!(errors.len(), 6, "{errors:?}");
    let kept: Vec<(&str, Option<Span>, usize)> = (module.decls.iter())
        .filter_map(|d| match d {
            Decl::Signature {
                name, syntax_error, ..
            } => {
                let equations = (module.decls.iter())
                    .filter(|e| matches!(e, Decl::Equation { name: n, .. } if n.text == name.text))
                    .count();
                Some((name.text.as_str(), *syntax_error, equations))
            }
            _ => None,
        })
        .collect();
    let at = |i: usize| errors[i].primary_span();
    assert_eq!(
        kept,
        [
            ("double", None, 1),
            ("doubleTwo", at(0), 1),
            ("arms", at(1), 1),
            ("trailing", at(2), 1),
            ("local", at(3), 1),
            ("last", None, 1),
        ]
    );
    // The error is where the parser reported it: the end of `(rfl`.
    let line = &text[..at(0).unwrap().start as usize];
    assert!(line.ends_with("(rfl"), "{line:?}");
    let signature = |name: &str| {
        module
            .decls
            .iter()
            .find(|d| matches!(d, Decl::Signature { name: n, .. } if n.text == name))
    };
    let Some(Decl::Signature { attrs, export, .. }) = signature("doubleTwo") else {
        panic!("{:?}", module.decls);
    };
    assert_eq!(attr_texts(attrs), ["simp"]);
    assert!(!export);
    assert!(matches!(
        signature("arms"),
        Some(Decl::Signature { export: true, .. })
    ));
    let failed: Vec<&str> = module.failed.iter().map(|n| n.name.text.as_str()).collect();
    assert_eq!(failed, ["header", "inst"]);
}

#[test]
fn attributes_on_types_constructors_and_fields() {
    let module = parse(
        "@[js.tag \"type\"] type Shape =\n  \
         | @[js.name \"DOT\"] Dot\n  \
         | @[js.name \"CIRCLE\", js.other] Circle (@[js.name \"center_x\"] x: Nat) [@[js.name \"n\"] n: Nat]\n\n\
         type R = { @[js.name \"type\"] kind: Text, size: Nat }\n",
    );
    let (on_type, on_ctors, on_fields) = data_attrs(&module.decls[0]);
    assert_eq!(on_type, ["js.tag \"type\""]);
    assert_eq!(
        on_ctors,
        [
            vec!["js.name \"DOT\""],
            vec!["js.name \"CIRCLE\"", "js.other"]
        ]
    );
    assert_eq!(
        on_fields,
        [
            vec![],
            vec![vec!["js.name \"center_x\""], vec!["js.name \"n\""]]
        ]
    );
    let (_, _, on_fields) = data_attrs(&module.decls[1]);
    assert_eq!(on_fields, [vec![vec!["js.name \"type\""], vec![]]]);
}

#[test]
fn a_multi_line_attribute_group_may_close_at_column_0() {
    let module = parse(
        "@[\n  js.tag \"type\",\n  js.other \"x\",\n]\n-- a comment\n\n@[js.more]\ntype T =\n  | A\n\ndef f: Nat := 1\n",
    );
    assert_eq!(module.decls.len(), 3);
    let (on_type, _, _) = data_attrs(&module.decls[0]);
    assert_eq!(on_type, ["js.tag \"type\"", "js.other \"x\"", "js.more"]);
    let Decl::Signature { attrs, .. } = &module.decls[1] else {
        panic!()
    };
    assert!(attrs.is_empty());
}

#[test]
fn attributes_before_a_definition_belong_to_its_signature() {
    let module = parse("@[js.name \"draw\"] export def render (n: Nat): Nat := n\n");
    let Decl::Signature { attrs, export, .. } = &module.decls[0] else {
        panic!()
    };
    assert!(*export);
    assert_eq!(attr_texts(attrs), ["js.name \"draw\""]);
}

#[test]
fn attributes_before_a_local_definition_belong_to_it() {
    // On the line before it, and on the same line.
    for text in [
        "def f (n: Nat): Nat :=\n  @[tailrec]\n  def g (m: Nat): Nat := m\n  g n\n",
        "def f (n: Nat): Nat :=\n  @[tailrec] def g (m: Nat): Nat := m\n  g n\n",
    ] {
        let module = parse(text);
        let Decl::Equation {
            rhs: Some(Expr::LocalDefs { defs, .. }),
            ..
        } = &module.decls[1]
        else {
            panic!("{text}: {:?}", module.decls[1])
        };
        let Decl::Signature { attrs, .. } = &defs[0].signature else {
            panic!()
        };
        assert_eq!(attr_texts(attrs), ["tailrec"], "{text}");
    }
}

#[test]
fn misplaced_attributes_are_refused() {
    for (text, code) in [
        // Attributes always attach to the next declaration, never drift.
        ("@[js.tag \"x\"]\nnamespace N\n", "E-ATTRIBUTE"),
        ("@[js.tag \"x\"]\nimport List (map)\n", "E-ATTRIBUTE"),
        ("@[js.tag \"x\"]\ntest \"t\" := True\n", "E-ATTRIBUTE"),
        (
            "@[js.tag \"x\"]\nability A where\n  op: Nat -> Nat\n",
            "E-ATTRIBUTE",
        ),
        ("def f (@[js.name \"x\"] n: Nat): Nat := n\n", "E-ATTRIBUTE"),
        (
            "def f: (@[js.name \"x\"] n: Nat) -> Nat := n => n\n",
            "E-ATTRIBUTE",
        ),
        (
            "def f: Nat -> Nat := (@[js.name \"x\"] n) => n\n",
            "E-ATTRIBUTE",
        ),
        ("type T (@[js.name \"x\"] a: Type) = | A\n", "E-ATTRIBUTE"),
        (
            "def f (n: Nat): Nat :=\n  @[tailrec] let m := n\n  m\n",
            "E-ATTRIBUTE",
        ),
        // The grammar: one name, then at most one plain string.
        ("@[js.name 123] type T = | A\n", "E-PARSE"),
        ("@[js.name \"x\" \"y\"] type T = | A\n", "E-PARSE"),
        ("@[] type T = | A\n", "E-PARSE"),
        ("@[js.name \"${1}\"] type T = | A\n", "E-PARSE"),
        ("@ type T = | A\n", "E-PARSE"),
        // Attributes with nothing after them.
        ("def f: Nat := 1\n\n@[js.tag \"x\"]\n", "E-PARSE"),
        (
            "def f: Nat := 1\n@[js.tag \"x\"]\n@[js.name \"y\"]\n",
            "E-PARSE",
        ),
    ] {
        let errors = parse_module_text(text).expect_err(text);
        assert_eq!(errors[0].code, code, "{text}: {:?}", errors[0].message);
    }
}

#[test]
fn an_unclosed_attribute_group_stops_at_the_next_declaration() {
    let text = "@[js.tag \"x\"\ntype T = | A\n\ndef f: Nat := 1\n";
    let mut sources = SourceMap::new();
    let file = sources.add("test.sw", text);
    let (module, errors) = parse_module_recovering(file, text, DEFAULT_STACK);
    assert_eq!(errors.len(), 1);
    // `T`, and `f`'s signature and equation.
    assert_eq!(module.decls.len(), 3, "{module:?}");
}

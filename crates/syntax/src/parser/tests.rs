//! The parser on its own.

use super::*;
use crate::SourceMap;
use crate::lexer::lex;

/// A parser over `text`'s tokens, recording marks.
fn with_parser<T>(text: &str, run: impl FnOnce(&mut Parser<'_>) -> T) -> T {
    let file = SourceMap::new().next_id();
    let tokens = lex(file, text).unwrap();
    let mut parser = Parser::new(
        &tokens,
        file,
        text.len(),
        StackLimit::from_here(DEFAULT_STACK),
    );
    run(&mut parser)
}

/// `recover_to` puts back every mode, and leaves the position and the
/// finished marks.
#[test]
fn recover_to_restores_the_modes() {
    with_parser("a + b * c", |parser| {
        parser.modes.limit = Some(2);
        let snapshot = parser.snapshot();
        parser.modes = Modes {
            in_list: true,
            limit: Some(4),
            allow: Some(1),
            calc_depth: 3,
            rewrite_rule: Some(1),
            guard_start: Some(2),
            rewrite_at: true,
            let_value: Some(0),
            recover: true,
            section_head: Some(1),
        };
        parser.pos = 3;
        parser.record(2, NodeKind::App);
        parser.recover_to(snapshot);
        assert_eq!(
            format!("{:?}", parser.modes),
            format!("{:?}", snapshot.modes)
        );
        assert_eq!(parser.modes.limit, Some(2));
        assert_eq!(parser.pos, 3);
        assert_eq!(parser.marks.len(), 1);
    });
}

/// An error recovered from fails the entry points that give one error
/// as if it had unwound, ahead of one that did.
#[test]
fn strict_fails_on_an_error_recovered_from() {
    with_parser("a b", |parser| {
        assert!(parser.strict(Ok(())).is_ok());
        parser.report(RecoveryPoint::Body, error(parser.here(), "first"));
        parser.report(RecoveryPoint::Body, error(parser.here(), "second"));
        let unwound: Result<()> = Err(Box::new(error(parser.here(), "unwound")));
        let failed = parser.strict(unwound).unwrap_err();
        assert_eq!(failed.message, "first");
        let failed = parser.strict(Ok(())).unwrap_err();
        assert_eq!(failed.message, "second");
        assert!(parser.strict(Ok(())).is_ok());
    });
}

/// The tree of the first declaration in `text`, in brackets: each node as
/// its kind and its children, each token as its source text, so
/// `(Binary a + (Binary b * c))` is `a + b * c`. Grammar tests compare these:
/// they pin how the parser groups tokens, which the lowering's tests don't.
fn sexp(text: &str) -> String {
    use crate::tree::Element;
    fn go(node: crate::tree::Node<'_>, text: &str, out: &mut String) {
        out.push('(');
        out.push_str(&format!("{:?}", node.kind()));
        for child in node.children() {
            out.push(' ');
            match child {
                Element::Node(n) => go(n, text, out),
                Element::Leaf(leaf) => out.push_str(&text[leaf.text_range()]),
            }
        }
        out.push(')');
    }
    let file = SourceMap::new().next_id();
    let tree = parse_tree(file, text, DEFAULT_STACK);
    let mut out = String::new();
    go(tree.decls().next().expect("a declaration"), text, &mut out);
    out
}

/// `*` binds tighter than `+`, which binds tighter than `=`.
#[test]
fn binary_operators_group_by_precedence() {
    assert_eq!(
        sexp("def f: Nat := a + b * c = d"),
        "(Def def f (ResultType : Nat) (Body := (Binary (Binary a + (Binary b * c)) = d)))"
    );
}

#[test]
fn or_is_looser_than_and_and_both_associate_right() {
    assert_eq!(
        sexp("def f: Bool := a || b && c"),
        "(Def def f (ResultType : Bool) (Body := (Binary a || (Binary b && c))))"
    );
    assert_eq!(
        sexp("def f: Bool := a && b && c"),
        "(Def def f (ResultType : Bool) (Body := (Binary a && (Binary b && c))))"
    );
}

#[test]
fn arrows_associate_right_and_iff_sits_between_arrow_and_or() {
    assert_eq!(
        sexp("def f: Prop := a && b -> c -> d"),
        "(Def def f (ResultType : Prop) (Body := (Arrow (Binary a && b) -> (Arrow c -> d))))"
    );
    assert_eq!(
        sexp("def f: Prop := p <-> q && r"),
        "(Def def f (ResultType : Prop) (Body := (Iff p <-> (Binary q && r))))"
    );
    assert_eq!(
        sexp("def f: Nat := a ≤ b ∧ b ≤ c → d"),
        "(Def def f (ResultType : Nat) (Body := (Arrow (Binary (Binary a ≤ b) ∧ (Binary b ≤ c)) → d)))"
    );
}

#[test]
fn a_comparison_chain_is_one_node() {
    assert_eq!(
        sexp("def f: Bool := a <= b < c"),
        "(Def def f (ResultType : Bool) (Body := (Chain a <= b < c)))"
    );
}

#[test]
fn pipes_associate_left() {
    assert_eq!(
        sexp("def f: Nat := xs |> f |> g"),
        "(Def def f (ResultType : Nat) (Body := (Pipe (Pipe xs |> f) |> g)))"
    );
}

#[test]
fn an_application_takes_dotted_and_bracketed_arguments() {
    assert_eq!(
        sexp("def f: Nat := f x.y (g z) w"),
        "(Def def f (ResultType : Nat) (Body := (App f (FieldAccess x . y) (Paren ( (App g z) )) w)))"
    );
}

#[test]
fn prefix_minus_and_bang_apply_to_one_operand_or_argument() {
    assert_eq!(
        sexp("def f: Int := -x.abs + 1"),
        "(Def def f (ResultType : Int) (Body := (Binary (Prefix - (FieldAccess x . abs)) + 1)))"
    );
    assert_eq!(
        sexp("def f: Int := f -x"),
        "(Def def f (ResultType : Int) (Body := (App f (Prefix - x))))"
    );
    assert_eq!(
        sexp("def f: Bool := !xs.isEmpty"),
        "(Def def f (ResultType : Bool) (Body := (Prefix ! (FieldAccess xs . isEmpty))))"
    );
    assert_eq!(
        sexp("def f: Nat := f !x"),
        "(Def def f (ResultType : Nat) (Body := (App f (Prefix ! x))))"
    );
}

#[test]
fn an_else_takes_the_closest_if() {
    assert_eq!(
        sexp("def f: Nat := if c then 1 else if d then 2 else 3"),
        "(Def def f (ResultType : Nat) (Body := (If if c then 1 else (If if d then 2 else 3))))"
    );
}

#[test]
fn lambdas_and_sections() {
    assert_eq!(
        sexp("def f: Nat := x y => x + y"),
        "(Def def f (ResultType : Nat) (Body := (Lambda x y => (Binary x + y))))"
    );
    assert_eq!(
        sexp("def f: Nat := (a, b) => a"),
        "(Def def f (ResultType : Nat) (Body := (Lambda (PatternTuple ( a , b )) => a)))"
    );
    assert_eq!(
        sexp("def f: Nat := xs.map (.double)"),
        "(Def def f (ResultType : Nat) (Body := (App (FieldAccess xs . map) (Paren ( (Section (FieldAccess . double)) )))))"
    );
    assert_eq!(
        sexp("def f: Nat := xs |> .map f"),
        "(Def def f (ResultType : Nat) (Body := (Pipe xs |> (Section (App (FieldAccess . map) f)))))"
    );
}

#[test]
fn tuples_lists_and_spreads() {
    assert_eq!(
        sexp("def f: Nat := (1, 2)"),
        "(Def def f (ResultType : Nat) (Body := (Tuple ( 1 , 2 ))))"
    );
    assert_eq!(
        sexp("def f: Nat := [1, ..xs]"),
        "(Def def f (ResultType : Nat) (Body := (List [ 1 , (Spread .. xs) ])))"
    );
}

#[test]
fn blocks_and_lets() {
    assert_eq!(
        sexp("def f: Nat :=\n  let y := 1\n  y + 2"),
        "(Def def f (ResultType : Nat) (Body := (Block (Let let y := 1) (Binary y + 2))))"
    );
    assert_eq!(
        sexp("def f: Nat := let (a, b) := e; a"),
        "(Def def f (ResultType : Nat) (Body := (LetExpr (Let let (PatternTuple ( a , b )) := e) ; a)))"
    );
}

#[test]
fn match_has_a_scrutinee_and_arms() {
    assert_eq!(
        sexp("def f: Nat := match n with\n  | 0 => a\n  | Succ m => b"),
        "(Def def f (ResultType : Nat) (Body := (Match match (Scrutinee n) with (Arm | 0 => a) (Arm | (PatternCtor Succ m) => b))))"
    );
    assert_eq!(
        sexp("def f: Nat := match o with | Some x | None => 0"),
        "(Def def f (ResultType : Nat) (Body := (Match match (Scrutinee o) with (Arm | (PatternOr (PatternCtor Some x) | None) => 0))))"
    );
}

#[test]
fn a_definition_with_arms_has_no_body() {
    assert_eq!(
        sexp("def f : Nat -> Nat\n  | 0 => 1\n  | Succ m => m"),
        "(Def def f (ResultType : (Arrow Nat -> Nat)) (Arms (Arm | 0 => 1) (Arm | (PatternCtor Succ m) => m)))"
    );
}

#[test]
fn a_header_has_its_parameters_result_type_and_body() {
    assert_eq!(
        sexp("def f (x: Nat) [n: Nat]: Nat := x"),
        "(Def def f (Param ( x : Nat )) (Param [ n : Nat ]) (ResultType : Nat) (Body := x))"
    );
    assert_eq!(
        sexp("theorem t (a: Nat): a = a := byComputing"),
        "(Theorem theorem t (Param ( a : Nat )) (ResultType : (Binary a = a)) (Body := byComputing))"
    );
}

#[test]
fn data_types_records_and_abilities() {
    assert_eq!(
        sexp("type T = | A | B (x: Nat)"),
        "(DataType type T = (Constructor | A) (Constructor | B (Binder ( x : Nat ))))"
    );
    assert_eq!(
        sexp("type R = { kind: Text, size: Nat }"),
        "(RecordType type R = (Fields { (Field kind : Text) , (Field size : Nat) }))"
    );
    assert_eq!(
        sexp("ability State (s : Type) where\n  get : () -> {State s} s"),
        "(Ability ability State (Binder ( s : Type )) where (AbilityOp get : (Arrow (Unit ( )) -> (Effect (Row { (App State s) }) s))))"
    );
}

#[test]
fn function_types_and_forall() {
    assert_eq!(
        sexp("def f: Nat := (x: Nat) -> Nat"),
        "(Def def f (ResultType : Nat) (Body := (FunctionType (Binder ( x : Nat )) -> Nat)))"
    );
    assert_eq!(
        sexp("def f: Prop := forall (a b: Nat) [c: Nat] => a + b = c -> p"),
        "(Def def f (ResultType : Prop) (Body := (Forall forall (LambdaParam ( a b : Nat )) (LambdaParam [ c : Nat ]) => (Arrow (Binary (Binary a + b) = c) -> p))))"
    );
}

#[test]
fn membership_and_constructor_fields() {
    assert_eq!(
        sexp("def f: Nat := a in xs"),
        "(Def def f (ResultType : Nat) (Body := (Membership a in xs)))"
    );
    assert_eq!(
        sexp("def f: Nat := C { x = 1, y }"),
        "(Def def f (ResultType : Nat) (Body := (CtorFields C (Record { (RecordField x = 1) , y }))))"
    );
}

#[test]
fn calc_and_rewrite() {
    assert_eq!(
        sexp("def f: Nat := calc\n  a\n  _ = b := h\n  _ = c := h2"),
        "(Def def f (ResultType : Nat) (Body := (Calc calc a (CalcStep _ = b := h) (CalcStep _ = c := h2))))"
    );
    assert_eq!(
        sexp("def f: Nat := rewrite h then x"),
        "(Def def f (ResultType : Nat) (Body := (Rewrite rewrite (RewriteRule h) then x)))"
    );
}

#[test]
fn namespace_and_import_lines() {
    assert_eq!(sexp("namespace A.B"), "(Namespace namespace A.B)");
    assert_eq!(
        sexp("import List (map, filter as f)"),
        "(Import import List ( (ImportItem map) , (ImportItem filter as f) ))"
    );
}

#[test]
fn attributes_belong_to_their_declaration() {
    assert_eq!(
        sexp("@[simp] theorem t: a = a := byComputing"),
        "(Theorem (Attributes @ [ (Attribute simp) ]) theorem t (ResultType : (Binary a = a)) (Body := byComputing))"
    );
}

#[test]
fn a_missing_operand_leaves_a_short_node() {
    assert_eq!(
        sexp("def f (x: Nat): Nat := x +"),
        "(Def def f (Param ( x : Nat )) (ResultType : Nat) (Body := (Binary x +)))"
    );
}

#[test]
fn an_error_keeps_what_finished_before_it() {
    assert_eq!(
        sexp("def f: Nat := xs.map (. + 1)"),
        "(Def def f (ResultType : Nat) (Body := (Error (FieldAccess xs . map) ( . + 1 ))))"
    );
}

/// A declaration in a file stops at the end of the declaration, since more
/// may follow; a lone expression stops at the end of its input.
#[test]
fn a_declaration_and_an_expression_name_their_end_differently() {
    let file = SourceMap::new().next_id();
    let expression = parse_expression(file, "1 +").unwrap_err();
    assert!(
        expression.message.contains("the end of the input"),
        "{}",
        expression.message
    );
    let (_, errors) = parse_module_recovering(file, "def f: Nat := 1 +\n", DEFAULT_STACK);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].message.contains("the end of the declaration"),
        "{}",
        errors[0].message
    );
}

/// A file whose first token is a column-0 `:=` is an error, and the
/// declarations after it still parse (SW-1918, review F11).
#[test]
fn a_file_starting_with_colon_eq_is_an_error() {
    let file = SourceMap::new().next_id();
    let (module, errors) = parse_module_recovering(file, ":= 1\ndef f: Nat := 0\n", DEFAULT_STACK);
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert_eq!(errors[0].code, "E-PARSE");
    assert_eq!(errors[0].message, "a declaration can't start with `:=`");
    assert!(!module.decls.is_empty(), "{:#?}", module.decls);
}

/// The expression table is loosest-binding first, so the prefix operators
/// come before application, and a pattern row isn't in it (SW-1918, review
/// F17). The layout section says how a numeral before `'` reads.
#[test]
fn the_syntax_doc_expression_table_is_loosest_first() {
    let docs = include_str!("../../../../docs/syntax.md");
    let expressions = docs
        .split("## Expressions")
        .nth(1)
        .expect("the expressions section")
        .split("\n## ")
        .next()
        .unwrap();
    let application = expressions
        .find("| `f a b` |")
        .expect("the application row");
    let prefix = expressions.find("| `!a` |").expect("the prefix not row");
    assert!(
        prefix < application,
        "`!a` binds looser than application, so its row comes first"
    );
    assert!(
        !expressions.contains("| `(-k)` |"),
        "`(-k)` is a pattern, so it isn't an expression-table row"
    );
    let layout = docs
        .split("## Layout")
        .nth(1)
        .expect("the layout section")
        .split("\n## ")
        .next()
        .unwrap();
    assert!(
        layout.contains("A numeral ends before a `'`"),
        "the layout section says how a numeral before `'` reads"
    );
}

/// A row starting the line after an arrow is a row wherever the line
/// starts, also at the block's own column, where the line continues the
/// arrow's (SW-3582); it used to read as a record applied to the type.
#[test]
fn a_row_on_the_line_after_its_arrow_is_a_row() {
    let row = "(Arrow (Unit ( )) → (Effect (Row { e }) a))";
    for text in [
        "def f: () → {e} a := x",
        "def f:\n  () →\n  {e} a := x",
        "def f:\n  () →\n    {e} a := x",
    ] {
        assert_eq!(
            sexp(text),
            format!("(Def def f (ResultType : {row}) (Body := x))"),
            "{text:?}"
        );
    }
    assert_eq!(
        sexp("def f (t:\n () →\n {e} a): Unit := ()"),
        format!("(Def def f (Param ( t : {row} )) (ResultType : Unit) (Body := (Unit ( ))))")
    );
}

/// `byWalking` at the end of the file used to bump past the last token
/// looking for its list of facts (the formatter fuzzer's seed 0x9e3779b97f4a7c15).
#[test]
fn a_by_walking_without_its_list_is_an_error() {
    for text in ["theorem e:(()):=byWalking", "theorem e:(()):=byWalking x"] {
        let file = SourceMap::new().add("input.sw", text);
        let error = crate::parse_module(file, text).expect_err(text);
        assert!(
            error.iter().any(|d| d.message.contains("expected `[`")),
            "{text:?}: {error:?}"
        );
    }
}

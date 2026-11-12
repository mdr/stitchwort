//! Indexed families in the surface language (docs/proposals/indexed-families.md
//! §7): what the examples under `examples/` don't pin down, chiefly
//! warnings, which they don't record, and smaller errors.

use stitchwort_cli::driver::Session;
use stitchwort_syntax::Diagnostic;

const VEC: &str = "type Vec (a: Type): Nat -> Type =\n  \
                   | VNil: Vec a 0\n  \
                   | VCons (x: a) (xs: Vec a n): Vec a (Succ n)\n\n";

fn load(text: &str) -> (Session, Result<(), Vec<Diagnostic>>) {
    let mut session = Session::new();
    let result = session.load("test.sw", text).map(|_| ());
    (session, result)
}

fn with_vec(rest: &str) -> String {
    format!("{VEC}{rest}")
}

fn error(text: &str) -> Diagnostic {
    let (_, result) = load(text);
    let errors = result.expect_err("should be rejected");
    errors.into_iter().next().expect("an error")
}

fn unreachable(session: &Session) -> Vec<&Diagnostic> {
    (session.warnings.iter())
        .filter(|w| w.code == "W-UNREACHABLE")
        .collect()
}

#[test]
fn an_arm_that_can_never_match_warns_and_is_dropped() {
    // The `VNil` arm's body isn't even well typed: it's never checked.
    let (session, result) = load(&with_vec(
        "def head: Vec a (Succ n) -> a\n  | VNil => 0\n  | VCons x _ => x\n",
    ));
    result.unwrap();
    let [w] = &unreachable(&session)[..] else {
        panic!("{:#?}", session.warnings);
    };
    assert_eq!(w.message, "this arm can never match");
    assert!(
        w.labels[0].message.contains("would need `Succ n = 0`"),
        "{w:?}"
    );
}

#[test]
fn an_arm_reached_in_another_branch_does_not_warn() {
    // `VNil, _` is dropped where the first vector is `VCons`, but it's the
    // `VNil` branch's arm.
    let (session, result) = load(&with_vec(
        "def f: Vec a n -> Vec a n -> Nat\n  | VNil, _ => 0\n  | VCons _ _, _ => 1\n",
    ));
    result.unwrap();
    assert!(unreachable(&session).is_empty(), "{:#?}", session.warnings);
}

#[test]
fn a_constructor_declared_with_n_plus_one_matches() {
    // `+` computes on its second argument too (SW-787): `n + 1` is `Succ n`.
    let (_, result) = load(
        "type Vec (a: Type): Nat -> Type =\n  | VNil: Vec a 0\n  \
         | VCons (x: a) (xs: Vec a n): Vec a (n + 1)\n\n\
         def head: Vec a (Succ k) -> a\n  | VCons x _ => x\n",
    );
    result.unwrap();
}

#[test]
fn stuck_sums_say_both_sides_are_unknown() {
    let e = error(&with_vec(
        "def lengthOfSum: Vec a (n + m) -> Nat\n  | VNil => 0\n  | VCons _ _ => 1\n",
    ));
    assert_eq!(e.code, "E-INDEX-STUCK");
    assert!(
        e.notes[0]
            .contains("so `n + m` doesn't compute while both are unknown: match on `n` first"),
        "{e:?}"
    );
}

#[test]
fn implicit_fields_by_name() {
    let (_, result) = load(&with_vec(
        "def one: Vec Nat 1 := VCons [n := 0] 5 VNil\n\
         def len: Vec a n -> Nat\n  | VNil => 0\n  | VCons [n := k] _ _ => Succ k\n\
         test \"len\" := len one == 1\n",
    ));
    result.unwrap();
    let e = error(&with_vec("def one: Vec Nat 1 := VCons [m := 0] 5 VNil\n"));
    assert_eq!(e.code, "E-UNKNOWN-NAME");
    let e = error(&with_vec(
        "def len: Vec a n -> Nat\n  | VNil => 0\n  | VCons k _ _ => Succ k\n",
    ));
    assert_eq!(e.code, "E-ARITY");
    assert!(e.notes[0].contains("[n := p]"), "{e:?}");
}

#[test]
fn declarations_need_their_parts() {
    let e = error("type Vec (a: Type): Nat -> Type =\n  | VNil\n");
    assert_eq!(e.code, "E-TYPE-MISMATCH");
    assert!(e.message.contains("needs a result type"), "{e:?}");
    let e = error("type R: Nat -> Type = { x: Nat }\n");
    assert_eq!(e.code, "E-RECORD-INDICES");
    // A type without indices may write its constructors' result types.
    let (_, result) = load("type T (a: Type) =\n  | MkT (x: a): T a\n");
    result.unwrap();
}

/// The `W-UNREACHABLE` warnings of the program `text`: the library has
/// none of its own.
fn written_unreachable(text: &str) -> Vec<Diagnostic> {
    let (session, result) = load(text);
    result.unwrap();
    unreachable(&session).into_iter().cloned().collect()
}

const MOVES: &str = "import Std (Bool, Eq, Void)\n\ntype Move = | Rock | Paper | Scissors\n\n\
                     def beats: Move -> Move -> Bool\n  \
                     | Rock, Scissors => True\n  | Paper, Rock => True\n  \
                     | Scissors, Paper => True\n  | _, _ => False\n\n";

#[test]
fn an_arm_whose_case_a_hypothesis_rules_out_warns() {
    let found = written_unreachable(&format!(
        "{MOVES}theorem only (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=\n  \
         match theirs with\n    \
         | Rock => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Paper => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Scissors => rfl\n"
    ));
    let messages: Vec<_> = found
        .iter()
        .map(|w| (w.message.as_str(), w.labels[0].message.as_str()))
        .collect();
    assert_eq!(
        messages,
        vec![
            (
                "this case can't happen",
                "here `h` is `False = True`, which can't hold"
            ),
            (
                "this case can't happen",
                "here `h` is `False = True`, which can't hold"
            ),
        ],
        "{found:#?}"
    );
}

#[test]
fn an_impossible_equation_says_what_its_sides_compute_to() {
    // `Nat.compare 0 0` computes to `Equal`, so the hypothesis is
    // `Equal = Less`: the label says that too, not only the call as written.
    let found = written_unreachable(
        "import Std (Bool, Eq, Nat, Ordering, Void)\n\n\
         theorem computed (h: Nat.compare 0 0 = Less) (b: Bool): b = b :=\n  \
         match b with\n    | True => rfl\n    | False => rfl\n",
    );
    let messages: Vec<_> = found
        .iter()
        .map(|w| (w.message.as_str(), w.labels[0].message.as_str()))
        .collect();
    assert_eq!(
        messages,
        vec![(
            "this case can't happen",
            "here `h` is `Nat.compare 0 0 = Less`, that is `Equal = Less`, which can't hold"
        )],
        "{found:#?}"
    );
}

#[test]
fn an_arm_that_uses_its_own_impossible_variable_does_not_warn() {
    // `p` is bound by the arm: no hypothesis rules the case out beforehand.
    let found = written_unreachable(&format!(
        "{MOVES}theorem noWin (h: beats Rock Rock): 1 = 2 :=\n  match h with\n    | q => Void.exfalso (Bool.falseNotTrue q)\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn an_arm_possible_in_one_branch_does_not_warn() {
    // The `Paper | Scissors` arm covers `Scissors` too, where `h` holds: its
    // `Paper` alternative warns, not the arm.
    let found = written_unreachable(&format!(
        "{MOVES}theorem only (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=\n  \
         match theirs with\n    \
         | Rock => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Paper | Scissors => cases\n"
    ));
    let notes: Vec<_> = found.iter().map(|w| w.notes[0].as_str()).collect();
    assert_eq!(
        notes,
        vec![
            "the arm can be deleted",
            "this alternative of the pattern can be deleted"
        ],
        "{found:#?}"
    );
}

#[test]
fn an_arm_a_later_arm_would_cover_does_not_warn() {
    // Without the `Rock` arm, `_` would take `Rock`, where `rfl` fails.
    let found = written_unreachable(&format!(
        "{MOVES}theorem only (theirs: Move) (h: beats Rock theirs): theirs = Scissors :=\n  \
         match theirs with\n    \
         | Rock => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Paper => Void.exfalso (Bool.falseNotTrue h)\n    \
         | _ => rfl\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn the_last_arm_of_a_match_ruled_out_whole_does_not_warn() {
    // A `match` with no arms can't be written: the first two arms warn,
    // the last stays.
    let found = written_unreachable(&format!(
        "{MOVES}theorem never (theirs: Move) (h: beats Rock theirs) (e: theirs = Rock): Void :=\n  \
         match theirs with\n    \
         | Rock => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Paper => Void.exfalso (Bool.falseNotTrue h)\n    \
         | Scissors => Void.exfalso (Bool.trueNotFalse (Eq.cong (m => beats Rock m) e))\n"
    ));
    assert_eq!(found.len(), 2, "{found:#?}");
}

/// The patterns of the arms each `W-UNREACHABLE` of `text` points at.
fn unreachable_arms(text: &str) -> Vec<String> {
    (written_unreachable(text).iter())
        .map(|w| {
            let span = w.labels[0].span;
            let arm = &text[span.start as usize..span.end as usize];
            arm.split(" =>").next().unwrap_or(arm).to_string()
        })
        .collect()
}

/// The whole underlined arm text of each `W-UNREACHABLE` of `text`.
fn unreachable_arm_text(text: &str) -> Vec<String> {
    (written_unreachable(text).iter())
        .map(|w| {
            let span = w.labels[0].span;
            text[span.start as usize..span.end as usize].to_string()
        })
        .collect()
}

#[test]
fn a_character_arm_a_hypothesis_rules_out_warns() {
    // In the `_` arm, `found` computes to `None = Some n`; left out, the
    // characters other than 'a' are a missing case the checker fills in the
    // same way (SW-2990), so the arm can be deleted.
    let with_arm = "import Std (Char, Eq, Nat, Option, Void)\n\n\
                    def command (key: Char): Option Nat :=\n  \
                    match key with\n    | 'a' => Some 1\n    | _ => None\n\n\
                    theorem onlyA (key: Char) (n: Nat) (found: command key = Some n): key = 'a' :=\n  \
                    match key with\n    | 'a' => rfl\n    \
                    | _ => Void.exfalso (Option.noneNotSome n found)\n";
    assert_eq!(unreachable_arms(with_arm).len(), 1);
    let without = with_arm.replace("    | _ => Void.exfalso (Option.noneNotSome n found)\n", "");
    let (_, result) = load(&without);
    result.unwrap_or_else(|e| panic!("{e:#?}"));
}

const AGREES: &str = "import Std (Bool, Eq, List, Nat, Void)\n\n\
                      def Agrees: List Nat -> List Nat -> Prop\n  \
                      | [], [] => Void\n  | [], [y, ..ys] => Void\n  \
                      | [x, ..xs], [] => Void\n  | [x, ..xs], [y, ..ys] => x = y\n\n\
                      def isNil: List Nat -> Bool\n  | [] => True\n  | _ => False\n\n";

#[test]
fn arms_that_can_go_only_one_at_a_time_warn_one_at_a_time() {
    // Either `[]` arm can be deleted, but not both: that leaves `[], _`,
    // where `Agrees [] ys` doesn't compute. The last one warns.
    let text = format!(
        "{AGREES}theorem notNil (xs ys: List Nat) (h: Agrees xs ys): isNil xs = False :=\n  \
         match xs, ys with\n    \
         | [], [] => Void.exfalso h\n    \
         | [], [y, ..ys] => Void.exfalso h\n    \
         | [x, .._], _ => rfl\n"
    );
    assert_eq!(unreachable_arms(&text), vec!["| [], [y, ..ys]"]);
    let without = text.replace("    | [], [y, ..ys] => Void.exfalso h\n", "");
    assert!(unreachable_arms(&without).is_empty());
}

#[test]
fn arms_that_take_each_others_cases_warn_together() {
    // Without the `Succ a, b` arm, `a, Succ b` would take `Succ a, Succ b`:
    // the two go together, and both can.
    let text = "import Std (Bool, Eq, Nat, Void)\n\n\
                def isZero: Nat -> Bool\n  | Zero => True\n  | Succ _ => False\n\n\
                theorem bothZero (a b: Nat) (h: isZero a = True) (k: isZero b = True): a + b = 0 :=\n  \
                match a, b with\n    \
                | Zero, Zero => rfl\n    \
                | Succ a, b => Void.exfalso (Bool.falseNotTrue h)\n    \
                | a, Succ b => Void.exfalso (Bool.falseNotTrue k)\n";
    let mut found = unreachable_arm_text(text);
    found.sort();
    assert_eq!(
        found,
        vec![
            "| Succ a, b => Void.exfalso (Bool.falseNotTrue h)",
            "| a, Succ b => Void.exfalso (Bool.falseNotTrue k)",
        ]
    );
    let (_, result) = load(
        "import Std (Bool, Eq, Nat, Void)\n\n\
         def isZero: Nat -> Bool\n  | Zero => True\n  | Succ _ => False\n\n\
         theorem bothZero (a b: Nat) (h: isZero a = True) (k: isZero b = True): a + b = 0 :=\n  \
         match a, b with\n    | Zero, Zero => rfl\n",
    );
    result.unwrap();
}

#[test]
fn the_cases_of_cases_do_not_warn() {
    // `cases` splits `theirs` itself; the impossible cases it makes aren't
    // arms anyone wrote.
    let found = written_unreachable(&format!(
        "{MOVES}theorem only (theirs: Move) (h: beats Rock theirs): theirs = Scissors := cases\n"
    ));
    assert!(found.is_empty(), "{found:#?}");
}

#[test]
fn a_number_case_left_out_is_impossible_when_a_hypothesis_computes_to_false() {
    // In the default, `n` is known to be neither 0 nor 1, so `isSmall n`
    // computes to `False`. What `n < 2` says isn't used: that needs a
    // decision procedure the checker doesn't have.
    let text = "import Std (Bool, Eq)\n\n\
                def isSmall: Nat -> Bool\n  | 0 => True\n  | 1 => True\n  | _ => False\n\n\
                def small (n: Nat) (h: isSmall n = True): Nat :=\n  \
                match n with\n    | 0 => 10\n    | 1 => 11\n";
    let (_, result) = load(text);
    result.unwrap_or_else(|e| panic!("{e:#?}"));
    let order = text.replace("(h: isSmall n = True)", "(h: n < 2)");
    assert_eq!(error(&order).code, "E-NONEXHAUSTIVE");
}

#[test]
fn a_number_case_left_out_is_impossible_when_a_variable_is_empty() {
    let text = "import Std (Void)\n\n\
                def small (n: Nat) (h: Void): Nat :=\n  \
                match n with\n    | 0 => 10\n    | 1 => 11\n";
    let (_, result) = load(text);
    result.unwrap_or_else(|e| panic!("{e:#?}"));
}

#[test]
fn a_number_case_that_can_happen_is_still_missing() {
    let text = "def small (n: Nat) (h: n < 5): Nat :=\n  \
                match n with\n    | 0 => 10\n    | 1 => 11\n";
    let e = error(text);
    assert_eq!(e.code, "E-NONEXHAUSTIVE");
    assert!(
        e.message.ends_with("matches numbers other than 0 and 1"),
        "{}",
        e.message
    );
}

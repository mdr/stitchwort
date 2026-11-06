//! `stitchwort search`'s matching (SW-915, docs/proposals/search.md draft 3
//! §5.1, §8 S1a), on a small file: the three relations and their order, a
//! written `_` free to take structure (D2064), targets headed by one of a
//! theorem's variables (D2067), named holes under the pattern's binders,
//! and the patterns refused.

use stitchwort_driver::driver::{Session, with_session};
use stitchwort_driver::search::{Options, Report, Scope};

const STACK: usize = 64 * 1024 * 1024;

/// `f` is opaque, so a call of it is only equal to a call with equal
/// arguments: the relations below can't be reached by computing it.
const SOURCE: &str = "\
opaque def f (x: Nat) (y: Nat): Nat := x

theorem fSelf (n: Nat): f n n = n unfolding f := rfl

theorem fAny (a: Nat) (b: Nat): f a b = a unfolding f := rfl

theorem fZero: f 0 0 = 0 unfolding f := rfl

theorem fSucc (n: Nat): f (Succ n) 1 = Succ n unfolding f := rfl

theorem pAt (p: Nat → Prop) (h: (n: Nat) → p n) (k: Nat): p k := h k

theorem anything (p: Prop) (h: p): p := h

theorem myTrans (x: Nat) (y: Nat) (z: Nat) (h1: x ≤ y) (h2: y ≤ z): x ≤ z := omega

theorem notTrans (x: Nat) (y: Nat) (z: Nat) (h1: x ≤ y) (h2: x ≤ z): x ≤ z := h2
";

/// Searches the file for `query`: the report, or the error's code.
fn search(query: &str) -> Result<Report, String> {
    with_session(STACK, Session::for_stack, |session| {
        session.load("search.sw", SOURCE).expect("the file checks");
        session
            .search(query, &Options::default(), &Scope::File)
            .map_err(|d| d.code.to_string())
    })
}

/// Each result's name (without `Main.`), relation and place.
fn rows(report: &Report) -> Vec<(String, &'static str, &'static str)> {
    (report.results.iter())
        .map(|r| {
            let name = r.name.strip_prefix("Main.").unwrap_or(&r.name).to_string();
            (name, r.relation.unwrap(), r.place.unwrap())
        })
        .collect()
}

#[test]
fn matches_are_ranked_instance_then_generalisation_then_common_instance() {
    let report = search("f ?x ?x = _").unwrap();
    assert_eq!(report.search_tier, Some("filtered"));
    let rows = rows(&report);
    let named: Vec<(&str, &str)> = (rows.iter())
        .filter(|(n, _, _)| n.starts_with("f") && n != "f.unfold")
        .map(|(n, r, _)| (n.as_str(), *r))
        .collect();
    assert_eq!(
        named,
        [
            // Only the theorem's variables took structure; `fAny`'s two
            // were made one, so it is less specific than `fSelf`.
            ("fSelf", "instance"),
            ("fAny", "instance"),
            // Only `?x` did (`?x := 0`).
            ("fZero", "generalisation"),
            // Both: `?x := Succ n`, and `n := 0` to make `Succ n` be 1.
            ("fSucc", "commonInstance"),
        ],
        "{rows:?}"
    );
}

#[test]
fn a_written_hole_takes_structure_without_lowering_the_relation() {
    // `_` takes `0` and `Succ n` as it asks to: every match is an instance
    // (D2064), the closer fits first.
    let report = search("f _ _ = _").unwrap();
    let rows = rows(&report);
    assert!(rows.iter().all(|(_, r, _)| *r == "instance"), "{rows:?}");
    assert_eq!(rows[0].0, "fSelf", "{rows:?}");
}

#[test]
fn a_target_headed_by_a_theorem_variable_is_tried_but_a_bare_one_is_not() {
    // `p k` is tried (D2067); `anything`'s conclusion, a bare `p`, would
    // match everything and isn't.
    let report = search(r#"(?q: Nat → Prop) 3, "Main.""#).unwrap();
    let rows = rows(&report);
    assert_eq!(
        rows,
        [("pAt".to_string(), "instance", "conclusion")],
        "{rows:?}"
    );
}

#[test]
fn named_holes_mean_the_same_under_the_patterns_binders() {
    // `?b` is one unknown at both arrows, so the transitivity pattern finds
    // `myTrans` first, its parameters in the theorem's order or not.
    let report = search(r#"(?a: Nat) ≤ ?b → ?b ≤ ?c → ?a ≤ ?c, "Main.""#).unwrap();
    let rows = rows(&report);
    assert_eq!(rows[0].0, "myTrans", "{rows:?}");
    // `notTrans` fits only with its `x` and `y` made one: after.
    let at = |name: &str| rows.iter().position(|(n, _, _)| n == name);
    assert!(at("notTrans").is_none_or(|i| i > 0), "{rows:?}");
}

#[test]
fn a_pattern_that_is_a_hole_or_doesnt_elaborate_is_refused() {
    assert_eq!(search("_").err().as_deref(), Some("E-SEARCH-PATTERN"));
    assert_eq!(search("?x").err().as_deref(), Some("E-SEARCH-PATTERN"));
    assert_eq!(
        search("f _ _ = List.nope").err().as_deref(),
        Some("E-UNKNOWN-NAME")
    );
    assert_eq!(search("f _, g _").err().as_deref(), Some("E-SEARCH-QUERY"));
}

#[test]
fn rewrite_mode_takes_either_side_of_an_equation() {
    let options = Options {
        rewrite: true,
        ..Options::default()
    };
    let report = with_session(STACK, Session::for_stack, |session| {
        session.load("search.sw", SOURCE).expect("the file checks");
        session
            .search("f (Succ _) _", &options, &Scope::File)
            .unwrap()
    });
    let rows = rows(&report);
    assert_eq!(
        rows[0],
        ("fSucc".to_string(), "instance", "left"),
        "{rows:?}"
    );
    assert_eq!(report.results[0].equation, Some("eq"));
}

#[test]
fn the_relaxed_pass_lists_only_related_candidates() {
    // Nothing names both `f` and `Nat.min`: the relaxed pass runs. For a
    // pattern with premises it lists neither `pAt` (its `p k` takes any
    // pattern whole) nor anything that names neither (SW-935).
    let report = search(r#"(n: Nat) → f n n = n → Nat.min n n = n, "Main.""#).unwrap();
    assert_eq!(report.search_tier, Some("relaxed"), "{report:?}");
    let rows = rows(&report);
    assert!(
        !rows.iter().any(|(n, _, _)| n == "pAt" || n == "anything"),
        "{rows:?}"
    );
}

/// Overloaded operators with operands nothing types (SW-927).
const OVERLOADED: &str = "\
theorem textJoin (a: Text) (b: Text): a ++ b = b ++ a := ?
theorem listJoin (xs: List Nat) (ys: List Nat): xs ++ ys = ys ++ xs := ?
theorem natPlus (n: Nat): n + 0 = n := omega
theorem intPlus (n: Int): n + 0 = n := omega
";

fn overloaded(query: &str) -> Report {
    with_session(STACK, Session::for_stack, |session| {
        // The `?`s make the file fail to load; what checked stays, and the
        // unfinished theorems aren't searched, but their types are what
        // the patterns below need to elaborate against.
        let _ = session.load("overloaded.sw", OVERLOADED);
        session
            .search(query, &Options::default(), &Scope::File)
            .unwrap_or_else(|d| panic!("{query}: {} {}", d.code, d.message))
    })
}

fn names(report: &Report) -> Vec<String> {
    (report.results.iter())
        .filter_map(|r| r.name.strip_prefix("Main.").map(str::to_string))
        .collect()
}

#[test]
fn an_append_of_holes_is_tried_as_lists_and_as_texts() {
    // Nothing in `_ ++ _ = _` says lists or texts: both readings are
    // searched and merged.
    let report = overloaded("_ ++ _ = _");
    assert_eq!(
        report.query.resolutions,
        ["List.append ?1 ?2 = ?3", "Text.append ?0 ?1 = ?2"],
        "{:?}",
        report.query
    );
    // `List.length` says lists: the text reading doesn't elaborate, and the
    // pattern as written, whose `++` waits until `List.length` says lists
    // (stage 7), is the same as the list reading, so it is the only one.
    // Its last hole is `?5`: the waiting `++` made an unknown first.
    let report = overloaded("List.length (_ ++ _) = _");
    assert!(report.query.resolutions.is_empty(), "{:?}", report.query);
    assert_eq!(
        report.query.elaborated.as_deref(),
        Some("(?2 ++ ?3).length = ?5")
    );
}

#[test]
fn arithmetic_on_holes_is_tried_at_nat_and_at_int() {
    let report = overloaded(r#"_ + 0 = _, "Main.""#);
    let found = names(&report);
    assert!(found.contains(&"natPlus".to_string()), "{found:?}");
    assert!(found.contains(&"intPlus".to_string()), "{found:?}");
    // A leaf with a type decides the group: one reading.
    let report = overloaded("List.length _ + _ = _");
    assert!(report.query.resolutions.is_empty(), "{:?}", report.query);
}

/// `--in` (SW-993): only declarations in the namespaces given, the
/// namespace written in full; one that names nothing says so.
#[test]
fn in_limits_the_search_to_a_namespace() {
    let within = |namespaces: &[&str]| {
        with_session(STACK, Session::for_stack, |session| {
            session.load("search.sw", SOURCE).expect("the file checks");
            let options = Options {
                within: namespaces.iter().map(|n| n.to_string()).collect(),
                limit: usize::MAX,
                ..Options::default()
            };
            (session.search("_ ≤ _", &options, &Scope::File)).expect("searched")
        })
    };
    let report = within(&["Std.Nat"]);
    let found: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
    assert!(!found.is_empty());
    assert!(found.iter().all(|n| n.starts_with("Std.Nat.")), "{found:?}");
    let report = within(&["Main"]);
    let found: Vec<&str> = report.results.iter().map(|r| r.name.as_str()).collect();
    assert!(found.contains(&"Main.myTrans"), "{found:?}");
    assert!(found.iter().all(|n| n.starts_with("Main.")), "{found:?}");
    let report = within(&["Std.Na"]);
    assert!(report.results.is_empty());
    assert!(
        (report.warnings.iter()).any(|w| w.contains("no declaration is in Std.Na")),
        "{:?}",
        report.warnings
    );
}

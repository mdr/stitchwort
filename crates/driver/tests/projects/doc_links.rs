//! `W-DOC-LINK` (docs/proposals/documentation.md §7, D2149, D2153, SW-1042):
//! which doc links resolve, and that the library has no broken one.

use stitchwort_driver::driver::Session;
use stitchwort_syntax::Diagnostic;

/// The `W-DOC-LINK` warnings of `text` loaded as a file.
fn link_warnings(text: &str) -> Vec<Diagnostic> {
    let mut session = Session::new();
    session.load("test.sw", text).expect("checks");
    session
        .warnings
        .iter()
        .filter(|w| w.code == "W-DOC-LINK")
        .cloned()
        .collect()
}

fn messages(text: &str) -> Vec<String> {
    link_warnings(text).into_iter().map(|w| w.message).collect()
}

/// The library's docs have no broken link: loading every library file (which
/// fails a file with a `W-DOC-LINK`, as for the other warnings the library
/// keeps clean) and the core leaves none.
#[test]
fn the_library_has_no_broken_doc_links() {
    let session = Session::eager_from_source();
    let found: Vec<_> = session
        .warnings
        .iter()
        .filter(|w| w.code == "W-DOC-LINK")
        .map(|w| w.message.as_str())
        .collect();
    assert!(found.is_empty(), "{found:#?}");
}

/// A library file with a broken link doesn't load: the library keeps the
/// convention it asks of programs.
#[test]
fn a_library_file_with_a_broken_link_fails_to_load() {
    let broken = "--| See [`Nat.nothing`].\ndef Nat.libOne (n: Nat): Nat := n + 1\n";
    let Err(report) = Session::with_library_files(&[("A.sw", broken)], true, false) else {
        panic!("a library file with a broken doc link loaded");
    };
    assert!(report.contains("W-DOC-LINK"), "{report}");
    let fine = "--| See [`Nat.libOne`].\ndef Nat.libOne (n: Nat): Nat := n + 1\n";
    assert!(Session::with_library_files(&[("A.sw", fine)], true, false).is_ok());
}

#[test]
fn links_to_declarations_namespaces_and_the_library_resolve() {
    let text = "\
--| Doubles. After [`later`], like [`double`] itself, [`List.map`], [`Std.List.map`],
--| [`Nat`], [`Std`], the namespace [`List`], and [`Shape`] with its [`Circle`].
def double (n: Nat): Nat := n + n

--| A forward use.
def later (n: Nat): Nat := double n

type Shape = | Circle (r: Nat)
";
    assert_eq!(messages(text), Vec::<String>::new());
}

#[test]
fn a_link_that_names_nothing_is_a_warning_with_the_nearest_name() {
    let found = link_warnings(
        "--| See [`doubel`] and [`List.mapp`] and [`wholly.other`].\n\
         def double (n: Nat): Nat := n + n\n",
    );
    let shown: Vec<(&str, Option<&str>)> = found
        .iter()
        .map(|w| (w.message.as_str(), w.notes.first().map(String::as_str)))
        .collect();
    assert_eq!(
        shown,
        [
            (
                "the doc link `doubel` names nothing",
                Some("did you mean `double`?")
            ),
            (
                "the doc link `List.mapp` names nothing",
                Some("did you mean `List.map`?")
            ),
            ("the doc link `wholly.other` names nothing", None),
        ]
    );
    // At the link, brackets and all.
    let text = "--| See [`doubel`].\ndef double (n: Nat): Nat := n + n\n";
    let w = &link_warnings(text)[0];
    let span = w.labels[0].span;
    assert_eq!(&text[span.start as usize..span.end as usize], "[`doubel`]");
}

#[test]
fn only_bar_docs_and_name_shaped_backticked_names_are_links() {
    let text = "\
-- A note: [`nothere`] isn't checked.
def a: Nat := 1

--| Bare [nothere] and [x] are list notation; \"its `[` is; its `]`\"; [`not a name`],
--| [`1x`], [``] and [`ESC [`] are not names; an unclosed [`
def b: Nat := 2

def c: Nat := 3 --| trailing [`nothere`]
";
    assert_eq!(messages(text), Vec::<String>::new());
}

#[test]
fn a_link_on_the_declaration_itself_and_to_a_type_with_its_constructor_resolve() {
    let text = "\
--| A box; [`Box`] is its type and its constructor.
type Box = | Box (n: Nat)

--| Nothing but [`unbox`].
def unbox (n: Nat): Nat := n
";
    assert_eq!(messages(text), Vec::<String>::new());
}

#[test]
fn a_link_never_needs_an_import() {
    // `Option.map`'s file isn't imported, and `List` is a name in the
    // library, not in this file's scope.
    let text = "--| Like [`Option.map`] and [`Text.padLeft`].\ndef f: Nat := 1\n";
    assert_eq!(messages(text), Vec::<String>::new());
}

#[test]
fn links_in_a_file_with_an_error_are_not_reported() {
    let mut session = Session::new();
    let errors = session
        .load("test.sw", "--| See [`nothere`].\ndef f: Nat := missing\n")
        .expect_err("fails");
    assert!(errors.iter().all(|d| d.code != "W-DOC-LINK"), "{errors:#?}");
}

/// A core file with a broken link doesn't load either (SW-1046): the core is
/// a separate load path from the library files.
#[test]
fn a_core_doc_with_a_broken_link_fails_the_load() {
    let core = |link: &str| {
        format!(
            "{}\n--| See [`{link}`].\ndef coreLinkProbe (n: Nat): Nat := n\n",
            stitchwort_elab::prelude()
        )
    };
    let Err(report) = Session::try_with_prelude(&core("Nope.nothing")) else {
        panic!("a core doc with a broken link loaded");
    };
    assert!(report.contains("W-DOC-LINK"), "{report}");
    let fine = Session::try_with_prelude(&core("coreLinkProbe"));
    assert!(fine.is_ok(), "{:?}", fine.err());
}

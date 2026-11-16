//! The REPL's tab completion. What a position can write is worked out by
//! the language server's completion code ([`stitchwort_lsp::complete`]):
//! what is being typed, the items for names in scope and for members after
//! a dot, in the order an editor lists them. This module supplies the
//! session's side: the names in scope, and the members found by checking
//! the receiver with the same probe the server uses
//! ([`stitchwort_elab::Elaborator::probe_members`]).

use rustyline::completion::Pair;
use stitchwort_driver::at::{DUMMY, with_dummy};
use stitchwort_driver::driver::Session;
use stitchwort_driver::live::ScopeName;
use stitchwort_lsp::complete::{self, Typed};

/// The REPL's own commands.
pub const COMMANDS: [&str; 5] = [":t", ":q", ":quit", ":help", ":h"];

/// The candidates for the line's text up to `pos`, and the byte where the
/// replaced word starts.
pub fn complete(session: &mut Session, line: &str, pos: usize) -> (usize, Vec<Pair>) {
    let text = &line[..pos];
    if text.starts_with(':') && !text.contains(char::is_whitespace) {
        let found = COMMANDS.iter().filter(|c| c.starts_with(text));
        return (0, found.map(|c| pair(c, c)).collect());
    }
    // `:t expr` completes `expr`.
    let (base, text) = match text.strip_prefix(":t ") {
        Some(rest) => (3, rest),
        None => (0, text),
    };
    let (start, found) = match text.strip_prefix("import") {
        Some(rest) if rest.is_empty() || rest.starts_with(char::is_whitespace) => {
            import_candidates(session, rest)
        }
        _ => expression_candidates(session, text),
    };
    (base + start, found)
}

fn pair(label: &str, replacement: &str) -> Pair {
    Pair {
        display: label.to_string(),
        replacement: replacement.to_string(),
    }
}

/// The candidates for the end of an expression: a name in scope, or a member
/// after a dot. Returns where the typed word starts in `text`.
fn expression_candidates(session: &mut Session, text: &str) -> (usize, Vec<Pair>) {
    match complete::typed(text, text.len()) {
        Typed::Nothing => (text.len(), Vec::new()),
        Typed::Name { wanted } => {
            // What an import would bring is left out: a name that isn't in
            // scope can't be written by completing it.
            let names: Vec<ScopeName> = (session.elab.names_in_scope().into_iter())
                .filter(|n| n.import.is_none() && n.name.starts_with(wanted))
                .collect();
            let items = complete::scope_items(Vec::new(), &names, text, wanted);
            (text.len() - wanted.len(), pairs(items, wanted))
        }
        Typed::Member { dot, wanted, .. } => {
            let found = members(session, text, dot, wanted.len());
            let found: Vec<ScopeName> = (found.into_iter())
                // Most of a type's members are lemmas: they wait for a
                // first letter, as in the editor.
                .filter(|n| !(wanted.is_empty() && n.kind == "theorem"))
                .collect();
            (dot + 1, pairs(complete::member_items(&found), wanted))
        }
    }
}

/// The candidates after `import`: namespaces, then inside the brackets the
/// names of the namespace before them.
fn import_candidates(session: &mut Session, rest: &str) -> (usize, Vec<Pair>) {
    let offset = 6; // "import"
    if let Some((path, inside)) = rest.split_once('(') {
        let path = path.trim();
        let word = inside.rsplit([',', ' ', '(']).next().unwrap_or_default();
        let word_start = offset + rest.len() - word.len();
        let found = namespace_members(session, path)
            .into_iter()
            .filter(|n| n.kind != "theorem" || !word.is_empty())
            .collect::<Vec<_>>();
        return (word_start, pairs(complete::member_items(&found), word));
    }
    let word = rest.rsplit(char::is_whitespace).next().unwrap_or_default();
    let word_start = offset + rest.len() - word.len();
    let found = match word.rsplit_once('.') {
        Some((parent, _)) => {
            let child_start = word_start + parent.len() + 1;
            let found = namespace_members(session, parent);
            return (
                child_start,
                pairs(complete::member_items(&found), &word[parent.len() + 1..]),
            );
        }
        None => roots(session),
    };
    (word_start, pairs(complete::member_items(&found), word))
}

/// The namespaces an `import` can start with: `Std`, and the first
/// segments of the paths the library's names are imported from.
fn roots(session: &mut Session) -> Vec<ScopeName> {
    let mut names: Vec<String> = vec!["Std".to_string()];
    for n in session.elab.names_in_scope() {
        if let Some((path, _)) = n.import
            && let Some(first) = path.split('.').next()
            && !names.iter().any(|x| x == first)
        {
            names.push(first.to_string());
        }
    }
    names
        .into_iter()
        .map(|name| ScopeName {
            key: name.clone(),
            name,
            kind: "namespace",
            ty: None,
            own: false,
            import: None,
        })
        .collect()
}

/// The names in the namespace written `path`.
fn namespace_members(session: &mut Session, path: &str) -> Vec<ScopeName> {
    let text = format!("{path}.{DUMMY}");
    members(session, &text, path.len(), DUMMY.len())
}

/// What can follow the `.` at byte `dot` of the expression `text`, whose
/// typed part is `wanted` bytes: found by checking it with the dummy name
/// in its place.
fn members(session: &mut Session, text: &str, dot: usize, wanted: usize) -> Vec<ScopeName> {
    let probed = with_dummy(text, dot, wanted);
    let file = session.sources.next_id();
    session.elab.enable_navigation();
    session.elab.probe_members(file, (dot + 1) as u32);
    if let Ok(expr) = session.parse_expression("<completion>", &probed) {
        let _ = session.elab.infer_expr_type_only(&expr);
    }
    session.elab.take_probed_members().unwrap_or_default()
}

/// The items whose label starts with `wanted`, in the order the language
/// server gives them.
fn pairs(mut items: Vec<lsp_types::CompletionItem>, wanted: &str) -> Vec<Pair> {
    items.retain(|i| i.label.starts_with(wanted));
    items.sort_by(|a, b| a.sort_text.cmp(&b.sort_text));
    let mut seen = std::collections::BTreeSet::new();
    items.retain(|i| seen.insert(i.label.clone()));
    (items.iter()).map(|i| pair(&i.label, &i.label)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use stitchwort_driver::driver::with_session;

    const STACK: usize = 16 * 1024 * 1024;

    fn make(stack: usize) -> Session {
        let mut session = Session::for_stack(stack);
        session.use_test_std_cache();
        session
    }

    /// Runs `f` in a session on a thread with the stack its limits assume.
    fn in_session(f: impl FnOnce(&mut Session) + Send) {
        with_session(STACK, make, f);
    }

    fn labels(session: &mut Session, line: &str) -> (usize, Vec<String>) {
        let (start, found) = complete(session, line, line.len());
        (start, found.into_iter().map(|p| p.replacement).collect())
    }

    #[test]
    fn commands() {
        in_session(|s| {
            assert_eq!(labels(s, ":h"), (0, vec![":help".into(), ":h".into()]));
            assert_eq!(labels(s, ":q").1, [":q", ":quit"]);
        });
    }

    #[test]
    fn names_in_scope_include_the_sessions_own() {
        in_session(|s| {
            let (declared, _) = s
                .add_declarations("<input>", "def zebraCount: Nat := 3")
                .unwrap();
            assert_eq!(declared, ["zebraCount"]);
            let (start, found) = labels(s, "1 + zebra");
            assert_eq!((start, found), (4, vec!["zebraCount".to_string()]));
            // The prelude's names, too.
            assert!(labels(s, "Opti").1.contains(&"Option".to_string()));
            // And after `:t `.
            assert_eq!(labels(s, ":t zebra").0, 3);
        });
    }

    #[test]
    fn imports_bring_names() {
        in_session(|s| {
            assert!(!labels(s, "replic").1.contains(&"replicate".to_string()));
            assert!(
                s.add_imports("<input>", "import Std.List (replicate)")
                    .is_empty()
            );
            assert!(labels(s, "replic").1.contains(&"replicate".to_string()));
        });
    }

    #[test]
    fn namespaces_after_import() {
        in_session(|s| {
            assert!(labels(s, "import ").1.contains(&"Std".to_string()));
            assert_eq!(labels(s, "import St"), (7, vec!["Std".to_string()]));
            let (start, found) = labels(s, "import Std.Li");
            assert_eq!(start, 11);
            assert!(found.contains(&"List".to_string()), "{found:?}");
            let (start, found) = labels(s, "import Std.List (rep");
            assert_eq!(start, 17);
            assert!(found.contains(&"replicate".to_string()), "{found:?}");
        });
    }

    #[test]
    fn members_after_a_dot_by_the_receivers_type() {
        in_session(|s| {
            let (start, found) = labels(s, "[1, 2].le");
            assert_eq!(start, 7);
            assert!(found.contains(&"length".to_string()), "{found:?}");
            assert!(!found.contains(&"toUpper".to_string()));
            let (_, found) = labels(s, "[1, 2].");
            assert!(found.contains(&"map".to_string()), "{found:?}");
            // A session definition as the receiver.
            s.add_declarations("<input>", "def zs: List Nat := [3]")
                .unwrap();
            let (start, found) = labels(s, "zs.fil");
            assert_eq!(start, 3);
            assert!(found.contains(&"filter".to_string()), "{found:?}");
            // A namespace's members.
            let (_, found) = labels(s, "List.repl");
            assert!(found.contains(&"replicate".to_string()), "{found:?}");
        });
    }
}

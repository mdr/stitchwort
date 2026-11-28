//! `stitchwort/search` (docs/proposals/editor-type-search.md §6): a search
//! by type from an open document, as `stitchwort search --json` answers,
//! with what an editor needs to use each result: where it is, the name to
//! write, and the import the document needs for it.

use std::path::Path;
use std::sync::Arc;
use std::sync::atomic::AtomicBool;

use lsp_types::Url;
use stitchwort_driver::search::{Options, Report};
use stitchwort_driver::search_in::Searched;

use crate::source::Source;
#[cfg(target_family = "wasm")]
use crate::wasm::FileUrl as _;
use crate::{SearchTarget, library_uri, range, with_project_session};

/// The request: `{textDocument: {uri}, query, limit?, rewrite?}`.
pub(crate) const METHOD: &str = "stitchwort/search";

/// How many results the editor lists unless it asks for another number.
pub(crate) const LIMIT: usize = 50;

/// The answer to a search for `query` from the document `target` (named
/// `uri`): the report as `stitchwort search --json` prints it, each result
/// with `short`, `namespace`, `location`, `insertText` and
/// `additionalTextEdits` added; `{version, error: {code, message}}` for a
/// query that doesn't parse or elaborate; null when cancelled.
pub(crate) fn answer(
    server: &crate::Options,
    source: &dyn Source,
    target: SearchTarget,
    uri: &Url,
    query: &str,
    options: &Options,
    cancel: Arc<AtomicBool>,
) -> serde_json::Value {
    let text = target.text.clone();
    let (searched, project) = match target.project {
        Some((root, relative, open)) => {
            let base = source.files(&root);
            let files = stitchwort_driver::search_at::Overlay {
                base: &*base,
                texts: open,
            };
            let name = root
                .file_name()
                .map_or("project".to_string(), |n| n.to_string_lossy().into_owned());
            let cache = source.project_cache(&root);
            let searched =
                with_project_session(server, cache.as_deref(), true, cancel, |session| {
                    session.search_in_project(
                        &name,
                        &files,
                        &relative,
                        cache.as_deref(),
                        query,
                        options,
                    )
                });
            (searched, Some((root, name)))
        }
        // The warm session a project's search uses, library loaded: a query
        // typed a key at a time mustn't load the library at each key.
        None => {
            let name = (target.path.file_name())
                .and_then(|n| n.to_str())
                .unwrap_or("file.sw");
            let searched = with_project_session(server, None, true, cancel, |session| {
                session.search_in_text(name, &text, query, options)
            });
            (searched, None)
        }
    };
    let Some(searched): Option<Searched> = searched else {
        return serde_json::Value::Null;
    };
    match searched {
        Err(_cancelled) => serde_json::Value::Null,
        Ok(Err(d)) => serde_json::json!({
            "version": 1,
            "error": {"code": d.code, "message": d.message},
        }),
        Ok(Ok(report)) => {
            let place = Place {
                uri,
                project: project
                    .as_ref()
                    .map(|(root, name)| (root.as_path(), name.as_str())),
            };
            with_editing(&report, &text, &place)
        }
    }
}

/// Where a search ran from: the document, and in a project's file the
/// project's folder and the name its files are shown under.
pub(crate) struct Place<'a> {
    pub uri: &'a Url,
    pub project: Option<(&'a Path, &'a str)>,
}

/// `report` as JSON, each result with what [`answer`] adds, for the
/// document `text`.
pub(crate) fn with_editing(report: &Report, text: &str, place: &Place) -> serde_json::Value {
    let mut json = serde_json::to_value(report).unwrap_or_default();
    let own = own_namespace(text);
    if let Some(results) = json.get_mut("results").and_then(|r| r.as_array_mut()) {
        for result in results {
            let name = result["name"].as_str().unwrap_or_default().to_string();
            let import = result["import"].as_str().map(str::to_string);
            let edit = editing(&name, import.as_deref(), own.as_deref(), text);
            let (namespace, short) = name.rsplit_once('.').unwrap_or(("", &name));
            result["short"] = short.into();
            result["namespace"] = namespace.into();
            result["insertText"] = edit.insert.into();
            result["additionalTextEdits"] = serde_json::json!(edit.import);
            let file = result["file"].as_str().unwrap_or_default();
            let line = result["line"].as_u64().unwrap_or(1).saturating_sub(1) as u32;
            if let Some(uri) = file_uri(file, place) {
                result["location"] = serde_json::json!({
                    "uri": uri.as_str(),
                    "range": range([line, 0, line, 0]),
                });
            }
        }
    }
    json
}

/// What picking a result writes into the document.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Editing {
    /// The name as the document can write it once the import is there.
    pub insert: String,
    /// The import's edit, none when the document has it already.
    pub import: Vec<lsp_types::TextEdit>,
}

/// [`Editing`] for the result `name` whose import line is `import` (none
/// when the document needs none), in `text`, whose namespace is `own`.
pub(crate) fn editing(name: &str, import: Option<&str>, own: Option<&str>, text: &str) -> Editing {
    let parsed = import.and_then(|line| {
        let rest = line.strip_prefix("import ")?;
        let (namespace, item) = rest.split_once(" (")?;
        Some((namespace, item.strip_suffix(')')?))
    });
    match parsed {
        Some((namespace, item)) => {
            let insert = (name.strip_prefix(namespace))
                .and_then(|r| r.strip_prefix('.'))
                .unwrap_or(name)
                .to_string();
            let import = (stitchwort_driver::fixes::add_import(text, namespace, item))
                .map(|e| lsp_types::TextEdit::new(range(e.range), e.new_text))
                .into_iter()
                .collect();
            Editing { insert, import }
        }
        None => {
            let insert = own
                .and_then(|own| name.strip_prefix(own))
                .and_then(|r| r.strip_prefix('.'))
                .unwrap_or(name)
                .to_string();
            Editing {
                insert,
                import: Vec::new(),
            }
        }
    }
}

/// The namespace `text` declares: `Main` for a file that declares none.
fn own_namespace(text: &str) -> Option<String> {
    let declared = (text.lines())
        .find_map(|l| l.strip_prefix("namespace "))
        .map(|n| n.trim().to_string());
    Some(declared.unwrap_or_else(|| "Main".to_string()))
}

/// The document a result's `file` (as the search shows it) is: a library
/// file (`std/List/Toolkit.sw`, or its path on disk when the library is
/// read from a folder), a file of the project (`proj/src/…`), or the
/// document searched from.
fn file_uri(file: &str, place: &Place) -> Option<Url> {
    if let Some(std) = file.strip_prefix("std/") {
        return library_uri(std);
    }
    if Path::new(file).is_absolute() {
        return Url::from_file_path(file).ok();
    }
    if let Some((root, name)) = place.project
        && let Some(path) = file.strip_prefix(&format!("{name}/"))
    {
        let mut full = root.to_path_buf();
        full.extend(path.split('/'));
        return Url::from_file_path(full).ok();
    }
    Some(place.uri.clone())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_library_result_is_written_from_its_import_which_is_added() {
        let text = "namespace Demo\nimport Std (Nat)\n\ndef f: Nat := 1\n";
        let found = editing(
            "Std.List.filterMap",
            Some("import Std (List)"),
            Some("Demo"),
            text,
        );
        assert_eq!(found.insert, "List.filterMap");
        assert_eq!(found.import.len(), 1);
        assert_eq!(found.import[0].new_text, ", List");
        assert_eq!(found.import[0].range.start, lsp_types::Position::new(1, 15));
    }

    #[test]
    fn nothing_is_imported_twice_and_the_files_own_names_are_short() {
        let text = "namespace Demo\nimport Std (List, ..)\n";
        let found = editing("Std.List.filterMap", Some("import Std (List)"), None, text);
        assert_eq!(found.import, Vec::new());
        let own = editing("Demo.helper", None, Some("Demo"), text);
        assert_eq!(own.insert, "helper");
        let other = editing("Other.helper", None, Some("Demo"), text);
        assert_eq!(other.insert, "Other.helper");
    }
}

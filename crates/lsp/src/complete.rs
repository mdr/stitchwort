//! Name completion (the editor roadmap's row 1): the names a position can
//! write, from what the last check published, so that it answers at once
//! and while the text being typed doesn't parse.
//!
//! The candidates, in this order: the local variables bound earlier in the
//! declaration, the namespace's own declarations, then what the imports and
//! the defaults bring. While the declaration being edited doesn't parse,
//! the check has nothing for it, so its locals come from the last check in
//! which the file parsed: positions before the cursor are as they were.

use lsp_types::{CompletionItem, CompletionItemKind};
use stitchwort_driver::live::{FileAnswers, Place, ScopeName};

/// What the text before the cursor is being completed as.
#[derive(Debug, PartialEq, Eq)]
pub enum Typed<'t> {
    /// A name of its own: `wanted` is what is typed of it so far.
    Name { wanted: &'t str },
    /// After a dot: `before` is the text before the `.` (`xs`, `Std.List`,
    /// `(f x)`), ending at byte `dot`.
    Member {
        before: &'t str,
        dot: usize,
        wanted: &'t str,
    },
    /// Inside a comment or a string: nothing to complete.
    Nothing,
}

/// A character of a name (`x'`, `isEmpty?`, `step_2`).
pub fn name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\'' || c == '?'
}

/// What is being typed at byte `offset` of `text`.
pub fn typed(text: &str, offset: usize) -> Typed<'_> {
    let offset = offset.min(text.len());
    let line_start = text[..offset].rfind('\n').map_or(0, |i| i + 1);
    let line = &text[line_start..offset];
    if line.contains("--") || line.matches('"').count() % 2 == 1 {
        return Typed::Nothing;
    }
    let start = line
        .char_indices()
        .rev()
        .take_while(|(_, c)| name_char(*c))
        .last()
        .map_or(line.len(), |(i, _)| i);
    let wanted = &line[start..];
    match line[..start].strip_suffix('.') {
        Some(before) if before.ends_with(|c: char| name_char(c) || c == ')' || c == ']') => {
            Typed::Member {
                before,
                dot: line_start + start - 1,
                wanted,
            }
        }
        _ => Typed::Name { wanted },
    }
}

/// The completion kind for a declaration's kind.
pub fn item_kind(kind: &str) -> CompletionItemKind {
    match kind {
        "local" => CompletionItemKind::VARIABLE,
        "ctor" => CompletionItemKind::ENUM_MEMBER,
        "data" => CompletionItemKind::ENUM,
        "record" => CompletionItemKind::STRUCT,
        "interface" | "ability" => CompletionItemKind::INTERFACE,
        "op" => CompletionItemKind::METHOD,
        "field" => CompletionItemKind::FIELD,
        "namespace" => CompletionItemKind::MODULE,
        "theorem" => CompletionItemKind::CONSTANT,
        _ => CompletionItemKind::FUNCTION,
    }
}

/// An item's detail: its kind and, when known, its type, on one line.
pub fn detail(kind: &str, ty: Option<&str>) -> String {
    match ty.and_then(|t| t.lines().next()) {
        Some(ty) => format!("{kind}: {ty}"),
        None => kind.to_string(),
    }
}

/// Whether `[line, column]` comes before or at `at`.
fn before(a: (u32, u32), at: (u32, u32)) -> bool {
    a <= at
}

/// The local variables in scope at `at` in the file `place`: each name
/// once, the binder nearest the cursor, nearest first, with its type. From
/// `answers[0]`, the last check, if a declaration there is around `at`;
/// else from the others, checks of the file before its text broke, in
/// which the declaration around `at` is the last to start before it (the
/// text typed since may run past its end).
pub fn locals(
    answers: &[&FileAnswers],
    place: &Place,
    at: (u32, u32),
) -> Vec<(String, Option<String>)> {
    answers
        .iter()
        .enumerate()
        .map(|(i, file)| locals_in(file, place, at, i > 0))
        .find(|found| !found.is_empty())
        .unwrap_or_default()
}

/// [`locals`] from one check's answers: the binders before `at` in the
/// declaration around it, or with `older`, the last to start before it.
fn locals_in(
    file: &FileAnswers,
    place: &Place,
    at: (u32, u32),
    older: bool,
) -> Vec<(String, Option<String>)> {
    let inside = |r: [u32; 4]| before((r[0], r[1]), at) && before(at, (r[2], r[3]));
    let Some(decl) = (file.outline.iter())
        .filter(|o| o.parent.is_none())
        .filter(|o| match older {
            true => before((o.full_range[0], o.full_range[1]), at),
            // A declaration whose body didn't parse has no binders of its
            // body in this check, though its outline covers it (SW-3199):
            // the older checks know them.
            false => inside(o.full_range) && !o.body_error,
        })
        .map(|o| o.full_range)
        .max_by_key(|r| (r[0], r[1]))
    else {
        return Vec::new();
    };
    let within = |r: [u32; 4]| {
        before((decl[0], decl[1]), (r[0], r[1])) && before((r[2], r[3]), at) && !inside(r)
    };
    let mut binders: Vec<([u32; 4], &str, Option<&str>)> = Vec::new();
    for r in &file.refs {
        if r.kind != "local" || r.target.place != *place || !within(r.target.range) {
            continue;
        }
        match binders.iter_mut().find(|(b, ..)| *b == r.target.range) {
            Some(found) => {
                if found.2.is_none() {
                    found.2 = r.ty.as_deref();
                }
            }
            None => binders.push((r.target.range, r.name.as_str(), r.ty.as_deref())),
        }
    }
    binders.sort_by_key(|(r, ..)| std::cmp::Reverse((r[0], r[1])));
    let mut out: Vec<(String, Option<String>)> = Vec::new();
    for (_, name, ty) in binders {
        if !out.iter().any(|(n, _)| n == name) {
            out.push((name.to_string(), ty.map(str::to_string)));
        }
    }
    out
}

/// The items for a name of its own, `wanted` typed so far: the locals,
/// then `names` (the file's own first), each shown name once. Of the names
/// an import would bring, only those starting with `wanted`, once two
/// characters are typed (there are thousands): each adds its import to
/// `text`.
pub fn scope_items(
    locals: Vec<(String, Option<String>)>,
    names: &[ScopeName],
    text: &str,
    wanted: &str,
) -> Vec<CompletionItem> {
    let mut items: Vec<CompletionItem> = Vec::new();
    for (i, (name, ty)) in locals.into_iter().enumerate() {
        items.push(CompletionItem {
            label: name,
            kind: Some(CompletionItemKind::VARIABLE),
            detail: Some(detail("local", ty.as_deref())),
            sort_text: Some(format!("0{i:04}")),
            ..Default::default()
        });
    }
    let shadowed: std::collections::BTreeSet<String> =
        items.iter().map(|i| i.label.clone()).collect();
    let lower = wanted.to_lowercase();
    for n in names.iter().filter(|n| !shadowed.contains(&n.name)) {
        let Some((path, item)) = &n.import else {
            items.push(name_item(n, if n.own { '1' } else { '2' }));
            continue;
        };
        if wanted.chars().count() < 2 || !n.name.to_lowercase().starts_with(&lower) {
            continue;
        }
        let Some(edit) = crate::imports::add_import(text, path, item) else {
            continue;
        };
        let mut found = name_item(n, '3');
        found.label_details = Some(lsp_types::CompletionItemLabelDetails {
            detail: None,
            description: Some(format!("import {path} ({item})")),
        });
        found.additional_text_edits = Some(vec![edit]);
        items.push(found);
    }
    items
}

/// The item for a declaration in scope; `rank` sorts it among the others.
pub fn name_item(n: &ScopeName, rank: char) -> CompletionItem {
    CompletionItem {
        label: n.name.clone(),
        kind: Some(item_kind(n.kind)),
        detail: Some(detail(n.kind, n.ty.as_deref())),
        label_details: (n.key != n.name).then(|| lsp_types::CompletionItemLabelDetails {
            detail: None,
            description: Some(n.key.clone()),
        }),
        sort_text: Some(format!("{rank}{}", n.name)),
        ..Default::default()
    }
}

/// The items after a dot, in the order an editor should list them (it
/// shows a limited number, then filters by what is typed): fields; then
/// sub-namespaces, types, constructors, the other declarations and last
/// the theorems, each kind together; within a kind, the declarations of the first namespace
/// reached (the receiver's type's own) before the others (the extensions
/// and the types it unfolds to); within those, shorter names before
/// longer, then alphabetical. `found` comes in that namespace order.
pub fn member_items(found: &[ScopeName]) -> Vec<CompletionItem> {
    let mut namespaces: Vec<&str> = Vec::new();
    found
        .iter()
        .map(|n| {
            let home = n.key.strip_suffix(n.name.as_str()).unwrap_or_default();
            let group = match namespaces.iter().position(|h| *h == home) {
                Some(i) => i,
                None => {
                    namespaces.push(home);
                    namespaces.len() - 1
                }
            };
            let class = match n.kind {
                "field" => 0,
                "namespace" => 1,
                "data" | "record" | "interface" | "ability" => 2,
                "ctor" => 3,
                "theorem" => 5,
                _ => 4,
            };
            let mut item = name_item(n, '1');
            let length = n.name.chars().count();
            item.sort_text = Some(format!("{class}{:02}{length:03}{}", group.min(99), n.name));
            item
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn what_is_typed() {
        assert_eq!(
            typed("f xs.le", 7),
            Typed::Member {
                before: "f xs",
                dot: 4,
                wanted: "le"
            }
        );
        assert_eq!(
            typed("f xs.", 5),
            Typed::Member {
                before: "f xs",
                dot: 4,
                wanted: ""
            }
        );
        assert_eq!(typed("def f := Li", 11), Typed::Name { wanted: "Li" });
        assert_eq!(
            typed("x + 1.", 6),
            Typed::Member {
                before: "x + 1",
                dot: 5,
                wanted: ""
            }
        );
        assert_eq!(typed("x -- a.b", 8), Typed::Nothing);
        assert_eq!(typed("x . y", 5), Typed::Name { wanted: "y" });
    }
}

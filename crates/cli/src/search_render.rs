//! `stitchwort search`'s text output (SW-4936, D3763): one entry per result,
//! the short name and its type on the left, where it lives on the right, the
//! first sentence of its doc below. The JSON report (`--json`) carries the
//! rest (kind, relation, place, import line).

use stitchwort_driver::palette::{self, Role};
use stitchwort_driver::search::{Report, Result1};

/// How the report is laid out.
#[derive(Clone, Debug, Default)]
pub struct Layout {
    /// Colour with the process's palette (see [`crate::theme::init`]).
    pub color: bool,
    /// The terminal's width, when stdout is one. Without it, the location
    /// follows the type after two spaces.
    pub width: Option<usize>,
    /// The leading folder of a project file's name (the project's own,
    /// which the source names carry), dropped so that every path is
    /// relative to the project's root or the library's (`std/…`).
    pub strip: Option<String>,
    /// Whether the terminal shows italics, for docs.
    pub italic: bool,
}

const RESET: &str = "\x1b[0m";

struct Paint<'a>(&'a Layout);

impl Paint<'_> {
    fn role(&self, role: Role, extra: &str, text: &str) -> String {
        if !self.0.color || text.is_empty() {
            return text.to_string();
        }
        format!("\x1b[{}m{text}{RESET}", palette::current().sgr(role, extra))
    }

    /// `ty` coloured as code: type names, an ability's names inside `{ }`,
    /// numbers, and each punctuation mark and arrow.
    fn code(&self, ty: &str) -> String {
        if !self.0.color {
            return ty.to_string();
        }
        let mut out = String::new();
        let mut braces = 0usize;
        let chars: Vec<char> = ty.chars().collect();
        let mut i = 0;
        while i < chars.len() {
            let c = chars[i];
            if c.is_whitespace() {
                out.push(c);
                i += 1;
            } else if c.is_alphanumeric() || c == '_' {
                let start = i;
                while i < chars.len()
                    && (chars[i].is_alphanumeric()
                        || matches!(chars[i], '_' | '\'' | '!' | '?')
                        || (chars[i] == '.'
                            && chars.get(i + 1).is_some_and(|n| n.is_alphanumeric())))
                {
                    i += 1;
                }
                let word: String = chars[start..i].iter().collect();
                let role = if c.is_ascii_digit() {
                    Some(Role::Number)
                } else if c.is_uppercase() {
                    Some(if braces > 0 {
                        Role::Keyword
                    } else {
                        Role::Type
                    })
                } else {
                    None
                };
                match role {
                    Some(role) => out.push_str(&self.role(role, "", &word)),
                    None => out.push_str(&word),
                }
            } else {
                match c {
                    '{' => braces += 1,
                    '}' => braces = braces.saturating_sub(1),
                    _ => {}
                }
                out.push_str(&self.role(Role::Operator, "", &c.to_string()));
                i += 1;
            }
        }
        out
    }
}

/// The visible width of `text`: its characters, not its colour codes.
fn visible(text: &str) -> usize {
    let mut n = 0;
    let mut in_escape = false;
    for c in text.chars() {
        match (in_escape, c) {
            (true, 'm') => in_escape = false,
            (true, _) => {}
            (false, '\x1b') => in_escape = true,
            (false, _) => n += 1,
        }
    }
    n
}

/// What a result is, when it isn't a plain definition (`theorem`, `open
/// theorem`, `generated theorem`, `constructor`).
fn tag(r: &Result1) -> Option<String> {
    if r.kind == "definition" && !r.generated && !r.open {
        return None;
    }
    let mut words = Vec::new();
    if r.generated {
        words.push("generated");
    }
    if r.open {
        words.push("open");
    }
    words.push(r.kind);
    Some(words.join(" "))
}

/// The report as text: the count and the query, then each result, then the
/// `--limit` note and the warnings.
pub fn render(report: &Report, layout: &Layout) -> String {
    let p = Paint(layout);
    let mut out = String::new();
    let n = report.total;
    let query = p.code(&report.query.text);
    let head = match n {
        0 => "No matches for ".to_string(),
        1 => "1 match for ".to_string(),
        _ => format!("{n} matches for "),
    };
    out.push_str(&format!("{} {query}\n", p.role(Role::Comment, "", &head)));
    for r in &report.results {
        out.push('\n');
        out.push_str(&entry(&p, r, layout));
    }
    if report.budget.truncated {
        out.push('\n');
        out.push_str(&p.role(
            Role::Comment,
            "",
            &format!("showing {} (--limit N for more)", report.results.len()),
        ));
        out.push('\n');
    }
    for w in &report.warnings {
        out.push_str(&format!("warning: {w}\n"));
    }
    out
}

fn entry(p: &Paint, r: &Result1, layout: &Layout) -> String {
    let (namespace, short) = match r.name.rsplit_once('.') {
        Some((ns, short)) => (ns, short),
        None => ("", r.name.as_str()),
    };
    let mut left = format!(
        "{}{}{}",
        p.role(Role::Secondary, "1", short),
        p.role(Role::Operator, "", " : "),
        p.code(&r.ty)
    );
    if let Some(part) = &r.conjunct {
        left.push_str(&p.role(Role::Comment, "", &format!(" (its {part} conjunct)")));
    }
    let file = match &layout.strip {
        Some(prefix) => r.file.strip_prefix(prefix.as_str()).unwrap_or(&r.file),
        None => &r.file,
    };
    let mut right = String::new();
    for part in [
        tag(r),
        (!namespace.is_empty()).then(|| namespace.to_string()),
    ]
    .into_iter()
    .flatten()
    {
        right.push_str(&p.role(Role::Comment, "", &part));
        right.push_str("  ");
    }
    right.push_str(&p.role(Role::Comment, "", &format!("{file}:{}", r.line)));
    let mut out = String::new();
    let fits = layout
        .width
        .is_none_or(|w| visible(&left) + 2 + visible(&right) <= w);
    if fits {
        let pad = match layout.width {
            Some(w) => w - visible(&left) - visible(&right),
            None => 2,
        };
        out.push_str(&format!("{left}{}{right}\n", " ".repeat(pad)));
    } else {
        out.push_str(&format!("{left}\n    {right}\n"));
    }
    if let Some(summary) = &r.summary {
        let extra = if layout.italic { "3" } else { "" };
        out.push_str(&format!("    {}\n", p.role(Role::Text, extra, summary)));
    }
    out
}

/// The terminal's width in columns, when stdout is a terminal.
#[cfg(unix)]
pub fn terminal_width() -> Option<usize> {
    let size = rustix::termios::tcgetwinsize(std::io::stdout()).ok()?;
    (size.ws_col > 0).then_some(usize::from(size.ws_col))
}

#[cfg(not(unix))]
pub fn terminal_width() -> Option<usize> {
    None
}

/// Whether the terminal named by `TERM` shows italics.
pub fn terminal_italic() -> bool {
    !matches!(
        std::env::var("TERM").as_deref(),
        Ok("linux" | "dumb" | "vt100" | "vt220")
    )
}

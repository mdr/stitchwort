//! Completion of parameter names in a call (docs/proposals/named-arguments.md
//! §6.3): after `(` or `[` in the arguments of a function, the parameters
//! not given by name yet. Read from the text before the cursor and the
//! function's printed type, which the last published answers hold; the text
//! need not parse, as it often doesn't while it's being typed.

/// Where the cursor is: just after an opening bracket (and the start of a
/// name), in the arguments of `head`.
#[derive(Debug, PartialEq, Eq)]
pub struct Call {
    /// The bracket was `[`: implicit parameters are wanted.
    pub implicit: bool,
    /// The function, as written (`clampTo`, `xs.map`, `List.map`).
    pub head: String,
    /// The parameters already given by name.
    pub given: Vec<String>,
}

/// A parameter of a printed function type.
#[derive(Debug, PartialEq, Eq)]
pub struct Parameter {
    pub name: String,
    pub implicit: bool,
    pub ty: String,
    /// Its default value, as printed (`(step: Nat := 1)`).
    pub default: Option<String>,
}

const KEYWORDS: &[&str] = &[
    "def", "let", "in", "if", "then", "else", "match", "with", "test", "theorem", "return",
    "where", "by", "exists",
];

fn is_name_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_' || c == '\''
}

fn is_word_char(c: char) -> bool {
    is_name_char(c) || c == '.'
}

/// The call whose argument is being started at byte `offset` of `text`, if
/// the cursor is right after `(` or `[` and a partial name.
pub fn call_at(text: &str, offset: usize) -> Option<Call> {
    let before: Vec<char> = text.get(..offset)?.chars().collect();
    let mut i = before.len();
    while i > 0 && is_name_char(before[i - 1]) {
        i -= 1;
    }
    while i > 0 && before[i - 1].is_whitespace() {
        i -= 1;
    }
    let bracket = i.checked_sub(1)?;
    let implicit = match before[bracket] {
        '(' => false,
        '[' => true,
        _ => return None,
    };
    // The atoms of the application, back from the bracket: the leftmost
    // one is the function, if it is a name.
    let mut head: Option<(usize, usize)> = None;
    let mut at = bracket;
    loop {
        // Whitespace; a line break only into an indented line (a line at
        // column 0 starts something else).
        let from = at;
        let mut crossed_break = false;
        while at > 0 && before[at - 1].is_whitespace() {
            crossed_break |= before[at - 1] == '\n';
            at -= 1;
        }
        if at == 0 || (crossed_break && !line_is_indented(&before, from)) {
            break;
        }
        match before[at - 1] {
            ')' | ']' => {
                let mut depth = 0usize;
                let mut k = at;
                while k > 0 {
                    k -= 1;
                    match before[k] {
                        ')' | ']' | '}' => depth += 1,
                        '(' | '[' | '{' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                if depth != 0 {
                    return None;
                }
                head = None;
                at = k;
            }
            '"' => {
                at = before[..at - 1].iter().rposition(|&c| c == '"')?;
                head = None;
            }
            c if is_word_char(c) => {
                let end = at;
                while at > 0 && is_word_char(before[at - 1]) {
                    at -= 1;
                }
                let word: String = before[at..end].iter().collect();
                if KEYWORDS.contains(&word.trim_start_matches('.')) {
                    break;
                }
                head = Some((at, end));
            }
            _ => break,
        }
    }
    let (start, end) = head?;
    let word: String = before[start..end].iter().collect();
    let head = word.trim_start_matches('.').to_string();
    if head.is_empty() || head.starts_with(|c: char| c.is_ascii_digit()) {
        return None;
    }
    let arguments: String = before[end..bracket].iter().collect();
    Some(Call {
        implicit,
        head,
        given: given_names(&arguments),
    })
}

/// Whether the line that the text before `at` ends on starts with
/// whitespace.
fn line_is_indented(before: &[char], at: usize) -> bool {
    let start = before[..at]
        .iter()
        .rposition(|&c| c == '\n')
        .map_or(0, |k| k + 1);
    before
        .get(start)
        .is_some_and(|c| c.is_whitespace() && *c != '\n')
}

/// The names in `(x := …)` and `[x := …]` among the arguments in `call`
/// (not inside another argument).
fn given_names(call: &str) -> Vec<String> {
    let chars: Vec<char> = call.chars().collect();
    let mut names = Vec::new();
    let mut depth = 0usize;
    for k in 0..chars.len() {
        match chars[k] {
            '(' | '[' | '{' => {
                if depth == 0 && chars[k] != '{' {
                    let mut j = k + 1;
                    while j < chars.len() && chars[j].is_whitespace() {
                        j += 1;
                    }
                    let start = j;
                    while j < chars.len() && is_name_char(chars[j]) {
                        j += 1;
                    }
                    let end = j;
                    while j < chars.len() && chars[j].is_whitespace() {
                        j += 1;
                    }
                    if end > start && chars[j..].starts_with(&[':', '=']) {
                        names.push(chars[start..end].iter().collect());
                    }
                }
                depth += 1;
            }
            ')' | ']' | '}' => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    names
}

/// The named parameters of a printed function type
/// (`(low: Nat) -> [n: Nat] -> Nat`), in order.
pub fn parameters(ty: &str) -> Vec<Parameter> {
    let mut segments = Vec::new();
    let mut depth = 0i32;
    let mut start = 0;
    let bytes = ty.as_bytes();
    let mut k = 0;
    while k < bytes.len() {
        match bytes[k] {
            b'(' | b'[' | b'{' => depth += 1,
            b')' | b']' | b'}' => depth -= 1,
            b'-' if depth == 0 && bytes.get(k + 1) == Some(&b'>') => {
                segments.push(&ty[start..k]);
                start = k + 2;
                k += 1;
            }
            _ => {}
        }
        k += 1;
    }
    // What follows the last arrow is the result: not a parameter.
    segments
        .into_iter()
        .filter_map(|segment| {
            let segment = segment.trim();
            let implicit = match segment.chars().next()? {
                '(' => false,
                '[' => true,
                _ => return None,
            };
            let inner = segment.get(1..segment.len().checked_sub(1)?)?;
            let (name, ty) = inner.split_once(':')?;
            let name = name.trim();
            if name.is_empty() || name.starts_with('_') || !name.chars().all(is_name_char) {
                return None;
            }
            let (ty, default) = match ty.split_once(" := ") {
                Some((ty, default)) => (ty, Some(default.trim().to_string())),
                None => (ty, None),
            };
            Some(Parameter {
                name: name.to_string(),
                implicit,
                ty: ty.trim().to_string(),
                default,
            })
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    fn call(text: &str) -> Option<Call> {
        call_at(text, text.len())
    }

    #[test]
    fn finds_the_function_and_the_names_given() {
        let c = call("def a: Nat := clampTo (high := 9) (").unwrap();
        assert_eq!(c.head, "clampTo");
        assert!(!c.implicit);
        assert_eq!(c.given, ["high"]);
        let c = call("def a: Nat := pick [count := 3] [la").unwrap();
        assert!(c.implicit);
        assert_eq!(c.given, ["count"]);
    }

    #[test]
    fn plain_arguments_do_not_hide_the_function() {
        assert_eq!(call("def a := xs.map f (").unwrap().head, "xs.map");
        assert_eq!(call("def a := 5 |> clampTo (").unwrap().head, "clampTo");
        assert_eq!(call("def a := f (g 1) 2 (").unwrap().head, "f");
    }

    #[test]
    fn stops_at_the_start_of_a_declaration() {
        assert_eq!(call("def a := 1\ndef b := f (").unwrap().head, "f");
        assert_eq!(call("def a := f\n  (x := 1)\n  (").unwrap().head, "f");
        assert!(call("def a := f (1)\n(").is_none());
        assert!(call("def a := (").is_none());
    }

    #[test]
    fn nothing_after_something_else() {
        assert!(call("def a := f (x := 1").is_none());
        assert!(call("def a := f (x +").is_none());
    }

    #[test]
    fn reads_parameters_from_a_type() {
        let got = parameters("[n: Nat] -> (xs: Vec Nat n) -> (f: Nat -> Nat) -> Nat -> Nat");
        let names: Vec<(&str, bool, &str)> = got
            .iter()
            .map(|p| (p.name.as_str(), p.implicit, p.ty.as_str()))
            .collect();
        assert_eq!(
            names,
            [
                ("n", true, "Nat"),
                ("xs", false, "Vec Nat n"),
                ("f", false, "Nat -> Nat")
            ]
        );
    }

    #[test]
    fn reads_a_parameters_default() {
        let got = parameters("(start: Nat) -> (step: Nat := start + 1) -> List Nat");
        let defaults: Vec<(&str, &str, Option<&str>)> = got
            .iter()
            .map(|p| (p.name.as_str(), p.ty.as_str(), p.default.as_deref()))
            .collect();
        assert_eq!(
            defaults,
            [("start", "Nat", None), ("step", "Nat", Some("start + 1"))]
        );
    }
}

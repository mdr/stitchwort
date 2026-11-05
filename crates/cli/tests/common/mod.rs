//! Helpers shared by the CLI's test binaries.

#![allow(dead_code)] // each test binary uses some of these

/// The non-empty parts of an `EXAMPLES` filter, in order.
fn parts(filter: &str) -> impl Iterator<Item = &str> {
    filter
        .split(',')
        .map(str::trim)
        .filter(|part| !part.is_empty())
}

/// Fails when `EXAMPLES` is set and one of its parts matches none of `names`.
///
/// `EXAMPLES` keeps the names containing a part, so a part that matches
/// nothing runs no tests and passes silently: the nearest names turn a typo
/// into a failure that says what it meant. `names` is every name the binary
/// would check, so a part that only matches in another test's sweep still
/// counts.
pub fn check_examples_env(names: &[String], noun: &str) {
    let Ok(filter) = std::env::var("EXAMPLES") else {
        return;
    };
    if let Some(message) = filter_error(&filter, names, noun) {
        panic!("{message}");
    }
}

/// The message to fail with when an `EXAMPLES` part matches none of `names`,
/// or `None` when every non-empty part matches at least one.
pub fn filter_error(filter: &str, names: &[String], noun: &str) -> Option<String> {
    let missing: Vec<&str> = parts(filter)
        .filter(|part| !names.iter().any(|name| name.contains(part)))
        .collect();
    if missing.is_empty() {
        return None;
    }
    let suggestion = |part: &str| {
        let nearest = nearest_names(part, names);
        if nearest.is_empty() {
            String::new()
        } else {
            format!(" (did you mean {}?)", quoted(&nearest))
        }
    };
    let what = match missing.as_slice() {
        [part] if filter.trim() == *part => {
            format!("EXAMPLES={filter} matches no example{}", suggestion(part))
        }
        [part] => format!(
            "EXAMPLES={filter} has a part that matches no example: `{part}`{}",
            suggestion(part)
        ),
        parts => {
            let clauses: Vec<String> = parts
                .iter()
                .map(|part| format!("`{part}`{}", suggestion(part)))
                .collect();
            format!(
                "EXAMPLES={filter} has parts that match no example: {}",
                clauses.join(", ")
            )
        }
    };
    Some(format!("{what}; EXAMPLES filters by {noun}"))
}

/// The `limit` `names` closest to `part`, nearest first.
fn nearest_names<'a>(part: &str, names: &'a [String]) -> Vec<&'a str> {
    let mut ranked: Vec<(&str, usize)> = names
        .iter()
        .map(|name| (name.as_str(), distance(part, name)))
        .collect();
    ranked.sort_by(|a, b| a.1.cmp(&b.1).then_with(|| a.0.cmp(b.0)));
    ranked.into_iter().map(|(name, _)| name).take(3).collect()
}

/// The edit distance between `a` and `b`, in characters.
fn distance(a: &str, b: &str) -> usize {
    let a: Vec<char> = a.chars().collect();
    let b: Vec<char> = b.chars().collect();
    let mut previous: Vec<usize> = (0..=b.len()).collect();
    let mut current = vec![0; b.len() + 1];
    for (i, ca) in a.iter().enumerate() {
        current[0] = i + 1;
        for (j, cb) in b.iter().enumerate() {
            let substitution = previous[j] + usize::from(ca != cb);
            current[j + 1] = (previous[j + 1] + 1).min(current[j] + 1).min(substitution);
        }
        std::mem::swap(&mut previous, &mut current);
    }
    previous[b.len()]
}

/// `` `a`, `b` or `c` ``, for a message.
fn quoted(names: &[&str]) -> String {
    match names {
        [] => String::new(),
        [only] => format!("`{only}`"),
        [first, second] => format!("`{first}` or `{second}`"),
        _ => {
            let (last, rest) = names.split_last().unwrap();
            let rest: Vec<String> = rest.iter().map(|name| format!("`{name}`")).collect();
            format!("{} or `{last}`", rest.join(", "))
        }
    }
}

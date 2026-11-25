//! On/off switches read from environment variables.

/// Whether the environment variable `name` switches something on. Unset,
/// empty, `0` and `false` are off; anything else is on, so
/// `STITCHWORT_X=0` turns a switch off rather than on.
pub fn env_flag(name: &str) -> bool {
    env_flag_or(name, false)
}

/// Like [`env_flag`], for a switch that is on unless set off: `default`
/// applies only when the variable is unset.
pub fn env_flag_or(name: &str, default: bool) -> bool {
    match std::env::var_os(name) {
        None => default,
        Some(v) => !(v.is_empty() || v == "0" || v == "false"),
    }
}

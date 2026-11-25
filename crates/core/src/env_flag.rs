//! On/off switches read from environment variables.
//!
//! The implementation lives in `stitchwort_syntax::env_flag`, which `core`
//! depends on, so the lower crate can read its own switches; this is the same
//! helper under the path the rest of the workspace uses.

pub use stitchwort_syntax::env_flag::{env_flag, env_flag_or};

#[cfg(test)]
mod tests {
    use super::{env_flag, env_flag_or};

    /// A name no other test reads, since the environment is process-wide.
    const NAME: &str = "STITCHWORT_ENV_FLAG_TEST_SWITCH";

    #[test]
    #[allow(unsafe_code)] // set_var and remove_var are unsafe in edition 2024.
    fn unset_empty_zero_and_false_are_off() {
        // SAFETY: this is the only test that touches this variable, and no
        // other thread reads it while the test runs.
        unsafe {
            std::env::remove_var(NAME);
        }
        assert!(!env_flag(NAME));
        assert!(env_flag_or(NAME, true));

        for off in ["", "0", "false"] {
            // SAFETY: see above.
            unsafe {
                std::env::set_var(NAME, off);
            }
            assert!(!env_flag(NAME), "{off:?} should be off");
            assert!(!env_flag_or(NAME, true), "{off:?} should be off");
        }
        for on in ["1", "true", "yes"] {
            // SAFETY: see above.
            unsafe {
                std::env::set_var(NAME, on);
            }
            assert!(env_flag(NAME), "{on:?} should be on");
            assert!(env_flag_or(NAME, false), "{on:?} should be on");
        }

        // SAFETY: see above.
        unsafe {
            std::env::remove_var(NAME);
        }
    }
}

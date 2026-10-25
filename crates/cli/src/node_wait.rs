//! `run --js`'s side of the terminal (docs/proposals/terminal-io.md §4.7, §5):
//! waiting for Node, which puts the terminal back itself.

use std::sync::atomic::{AtomicU32, Ordering};

use nix::sys::signal::{self, SigSet, Signal};

/// The pid of the Node process of `run --js`, once started (0 before).
static NODE: AtomicU32 = AtomicU32::new(0);

/// Records the Node process that [`wait_for_node`]'s signal thread forwards
/// to.
pub fn set_node(pid: u32) {
    NODE.store(pid, Ordering::SeqCst);
}

/// For `run --js` (§4.7, §5): the terminal is Node's to put back, so this
/// process must outlive Node rather than die at the first Ctrl-C, or the
/// shell would get its prompt back before the terminal is restored. Blocks
/// `SIGINT`, `SIGTERM`, `SIGHUP` and `SIGQUIT` in this thread and so in the
/// threads after it (a child process starts with none blocked), and starts a
/// thread that swallows them: the terminal's own `SIGINT` and `SIGQUIT`
/// reach Node directly, and `SIGTERM` and `SIGHUP` sent to this process alone
/// are passed on to Node. Call before any other thread starts.
pub fn wait_for_node() {
    let mut set = SigSet::empty();
    for s in [
        Signal::SIGINT,
        Signal::SIGTERM,
        Signal::SIGHUP,
        Signal::SIGQUIT,
    ] {
        set.add(s);
    }
    if set.thread_block().is_err() {
        return;
    }
    let started = std::thread::Builder::new()
        .name("signals".into())
        .spawn(move || {
            while let Ok(caught) = set.wait() {
                let pid = NODE.load(Ordering::SeqCst);
                if matches!(caught, Signal::SIGTERM | Signal::SIGHUP)
                    && let Ok(pid) = i32::try_from(pid)
                    && pid > 0
                {
                    let _ = signal::kill(nix::unistd::Pid::from_raw(pid), caught);
                }
            }
        });
    if started.is_err() {
        let _ = set.thread_unblock();
    }
}

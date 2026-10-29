// SCRATCH (SW-787), not committed: loads the whole std eagerly, timed.
use stitchwort_driver::driver::Session;

#[test]
#[ignore]
fn sweep() {
    let t = std::time::Instant::now();
    let session = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(|| {
            let s = Session::eager();
            drop(s);
        })
        .unwrap()
        .join();
    eprintln!("EAGER-STD {:?} ok={}", t.elapsed(), session.is_ok());
}

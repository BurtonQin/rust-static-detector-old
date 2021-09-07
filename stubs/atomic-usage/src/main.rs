use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

fn main() {
    let a = AtomicUsize::new(1);
    output((move || {
        let d = a.load(Relaxed);
        if d == 1 {
            a.store(d + 1, Relaxed);
        };
        a.load(Relaxed)
    })());
}

fn output(i: usize) {
    println!("{}", i);
}

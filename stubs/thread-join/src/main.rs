use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread;

fn buggy() {
    let a = Arc::new(AtomicUsize::new(1));
    let a2 = Arc::clone(&a);
    let th1 = thread::spawn(move || a.store(2, Ordering::Relaxed));
    let th2 = thread::spawn(move || println!("{}", a2.load(Ordering::Relaxed)));
    th1.join().unwrap();
    th2.join().unwrap();
}

fn main() {
    buggy();
}

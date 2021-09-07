use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

struct Obj {
    atomic: Arc<AtomicUsize>,
}
impl Obj {
    fn new() -> Self {
        Self {
            atomic: Arc::new(AtomicUsize::new(1)),
        }
    }
    fn check(&self) {
        let a = &self.atomic;
        let b = Arc::clone(a);
        while a.load(Ordering::Relaxed) == 1 {
            match a.load(Ordering::Relaxed) {
                1 => b.store(2, Ordering::Relaxed),
                2 => self.atomic.store(3, Ordering::Relaxed),
                _ => self.atomic.store(4, Ordering::Relaxed),
            };
        }
    }
}
fn main() {
    let obj = Obj::new();
    obj.check();
}

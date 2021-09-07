use parking_lot::{Mutex, MutexGuard};
use std::sync::Arc;
use once_cell::sync::Lazy;

struct Wrapper<'a, T> {
    guard: MutexGuard<'a, T>,
    _other: i32,
}

impl<'a, T> Wrapper<'a, T> {
    fn wrap_struct(guard: MutexGuard<'a, T>) -> Self {
        Wrapper { guard, _other: 1 }
    }
    fn unwrap_struct(self) -> MutexGuard<'a, T> {
        self.guard
    }
}

static GLOBAL_MU: Lazy<Arc<Mutex<i32>>> = Lazy::new(|| {
    Arc::new(Mutex::new(1))
});

fn main() {
    let mu1 = Mutex::new(Box::new(1));
    let mu2 = Mutex::new(Box::new(2));
    let mut g1 = mu1.lock();
    let w1 = Wrapper::wrap_struct(g1);
    g1 = Wrapper::unwrap_struct(w1);
    let g3 = g1;
    let g2 = mu2.lock();
    let mut arr = [g3, g2];
    *arr[0] = Box::new(3);
    let mut g4 = GLOBAL_MU.lock();
    *g4 = 4;
}

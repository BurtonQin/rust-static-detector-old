use std::cell::UnsafeCell;

struct TestCell<T> {
    data: T,
}

impl<T> TestCell<T> {
    fn get(&self) -> *mut T {
        unsafe {
            self as *const TestCell<T> as *const T as *mut T
        }
    }
}

fn main() {
    let cell = TestCell { data: 1 };
    let ptr = cell.get();
    unsafe { *ptr = 2 };
    let cell2 = UnsafeCell::new(1);
    let ptr2 = cell2.get();
    unsafe { *ptr2 = 2 };
}

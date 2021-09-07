use std::marker::PhantomData;

struct Unique {
    pointer: *const i32,
    _marker: PhantomData<i32>,
}

impl Unique {
    pub fn as_ptr(self) -> *mut i32 {
        self.pointer as *mut i32
    }
}

fn main() {
    let u = Unique {
        pointer: &1 as *const i32,
        _marker: PhantomData,
    };
    let p = u.as_ptr();
    unsafe { *p += 1 };
}

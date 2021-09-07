struct Outer {
    inner: Inner,
}

struct Inner {
    p: *mut *mut i32,
}

impl Outer {
    fn new(mut d: *mut i32) -> Self {
        let inner = Inner {
               p: &mut d as *mut *mut i32,
           };
       Outer {
          inner, 
       }
    }

    fn change(&mut self) {
        unsafe { **self.inner.p = 1; }
    }
}

fn main() {
    let a = Box::new(1);
    let p = Box::into_raw(a);
    let mut outer = Outer::new(p);
    outer.change();
    unsafe { Box::from_raw(p); }
}

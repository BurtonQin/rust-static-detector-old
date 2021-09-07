struct Obj {
    inner: Vec<i32>,
}

impl Obj {
    fn buggy(&mut self, i: Option<i32>) {
        let p = match i {
            Some(_) => Vec::new().as_ptr(),
            None => std::ptr::null(),
        };
        unsafe {
            self.inner.push(*p);
        }
    }
}

fn main() {
    let mut obj = Obj { inner: Vec::new() };
    obj.buggy(Some(1));
}

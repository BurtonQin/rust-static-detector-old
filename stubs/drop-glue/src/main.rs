struct Obj {
    v: Vec<i32>,
}

impl Drop for Obj {
    fn drop(&mut self) {
        self.v.push(1);
    }
}

fn main() {
    let _obj = Obj {v: Vec::new()};
}

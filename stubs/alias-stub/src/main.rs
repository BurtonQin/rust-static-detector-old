struct Obj {
    data: Vec<i32>,
}
impl Obj {
    fn increase(&mut self) {
        self.data[0] += 1;
    }
    fn decrease(&self) {
        let d = &self.data[0];
        let x = &d;
        let _a = **x;
    }
}
fn foo(mut x: i32) {
    let y = &mut x;
    {
        let z: &i32 = &*y;
        my_print_i32(z);
    }
    *y = 32;
}
fn my_print_i32(i: &i32) {
    print!("{}", i);
}

fn main() {
    foo(12);
    let obj = Obj { data: vec![1] };
    obj.decrease();
}

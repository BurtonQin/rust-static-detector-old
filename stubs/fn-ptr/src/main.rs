fn add(a: i32, b: i32) -> i32 {
    a + b
}
fn buggy(func: &dyn Fn(i32, i32)->i32) -> i32 {
    func(1, 2)
}
fn main() {
    let p = add;
    buggy(&p);
    let p2 = |a: i32, b: i32| a + b;
    buggy(&p2);
}

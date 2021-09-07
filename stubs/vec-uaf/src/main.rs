fn buggy() -> *const i32 {
    let mut v = Vec::new();
    v.push(1);
    let p = v.as_mut_ptr();
    p
}
fn output(p: *const i32) {
    unsafe {
        println!("{:?}", *p);
    }
}
fn main() {
    let p = buggy();
    output(p);
}

struct Res {
    p: *mut i32,
    d: i32,
}
static mut GLOBAL: Res = Res {
    p: std::ptr::null_mut(),
    d: 0,
};
fn buggy(mut v: Vec<i32>) {
    let p = &mut v[0] as *mut i32;
    unsafe {
        *p = 2;
    }
    unsafe {
        GLOBAL = Res { p, d: 1 };
    }
}
fn main() {
    let v = vec![1];
    buggy(v);
}

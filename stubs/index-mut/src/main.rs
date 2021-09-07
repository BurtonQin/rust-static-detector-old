fn buggy(flag: bool, mut vec: Vec<i32>) -> *mut i32 {
    if flag {
        &mut vec[0]
    } else {
        &mut vec[1]
    }
}
fn main() {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    let p = buggy(true, v);
    unsafe { *p = 3; }
}


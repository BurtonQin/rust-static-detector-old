struct Obj<'a> {
    v: &'a mut [&'a i32]
}
fn main() {
    let mut vec = Vec::new();
    vec.push(&1);
    let mut o = Obj { v: &mut vec };
    // let r = &v[0];
    let r = &mut &mut o;
    let a = *((*r.v)[0]);
    print(a as f64);
    let d = &mut &mut o.v[0];
    print(***d as f64);
}

fn print(i: f64) {
    println!("{:?}", i);
}
fn foo(i: i32) -> Option<String> {
    if i < 42 {
        Some("Magic".to_owned())
    } else {
        None 
    }
}
fn bar(i: i32) -> Result<i32, String> {
    if i < 42 {
        Ok(i)
    } else {
        Err("Magic".to_owned())
    }
}
fn main() {
    let a = foo(42);
    a.unwrap();
    let b = bar(42);
    b.unwrap();
}

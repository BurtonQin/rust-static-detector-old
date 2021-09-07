fn fib_recur(n: i32) -> i32 {
    match n {
        0 => 0,
        1 => 1,
        x => fib_recur(x-1) + fib_recur(x-2),
    }
}

fn main() {
    println!("{}", fib_recur(10));
}

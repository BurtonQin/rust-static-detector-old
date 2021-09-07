static mut TIMES: u32 = 0;

fn buggy(u: u32) {
    println!("{}", u);
}

fn main() {
    unsafe {
        buggy(TIMES); 
    }
}

use std::cell::UnsafeCell;

struct Obj {
    data: UnsafeCell<i32>,
}

impl Obj {
    fn new() -> Self {
        Self {
            data: UnsafeCell::new(1),
        }
    }
    fn buggy(&self) {
        let p = self.data.get();
        unsafe { *p = 2 };
    }
}

struct Obj2 {
    data: UnsafeCell<String>,
}

impl Obj2 {
    fn new() -> Self {
        Self {
            data: UnsafeCell::new("1".to_string()),
        }
    }
    fn buggy(&self) {
        let p = self.data.get();
        unsafe { *p = "2".to_string() };
    }
}

trait CanAdd {
    fn addition(&self) {
        println!("trait addition");
    }
}

impl CanAdd for Obj {
    fn addition(&self) {
        println!("Obj addition");
    }
}

impl CanAdd for Obj2 {
    fn addition(&self) {
        println!("Obj2 addition");
    }
}

fn select(can_add: &dyn CanAdd) {
    can_add.addition();
}

fn addition<F>(func: F)
where
    F: Fn(),
{
    func();
}

fn main() {
    {
        let obj = Obj::new();
        addition(|| select(&obj));
    }
    {
        let obj2 = Obj2::new();
        addition(|| select(&obj2));
    }
}

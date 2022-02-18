fn main() {
    let v : i32 = 13;
    let mut w : i32 = 14;
    let z : i32 = 15;
    
    let a : &i32 = &v;
    let b : &mut i32 = &mut w;
    
    println!("The answer is {}", *a + *b + z);
    *b = 7; // Modify the contents of w
    *a = 5; // ERROR: a is not a mutable reference. (Indeed, v is not a mutable i32!)
}

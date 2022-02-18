fn main() {
    let v = 13;
    let mut w = 14;
    let z = 15;
    
    let a = &v;
    let b = &mut w;
    
    println!("The answer is {}", *a + *b + z);
    *b = 7; 
    *a = 5; // ERROR: ...
}

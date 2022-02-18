fn main() {
    let mut v = vec![20,21,22];
    {
        let a = &v; // immutable reference to v
        let b = &v; // immutable reference to v
        
        // ownership of v is now shared between a and b
        // v.push(22) // ERROR
        println!("The answer is {}", a[0] + b[2]);
        // ownership can be back with v
        // v.push(22) // OK
    }
    // ownership is now back with v
    v.push(24);
}

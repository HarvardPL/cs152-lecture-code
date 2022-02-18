fn main() {
    let mut a = &mut vec![0];
    {
        let mut v = vec![20,21,22];
        a = &mut v;
        a.push(23);
    } // vector object is deallocated here
    
    println!("The answer is {}", a[3]); // ERROR: use after free, since a outlives v
}

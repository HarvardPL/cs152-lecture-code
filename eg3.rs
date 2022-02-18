fn main() {
    let mut v = vec![20,21,22];
    {
        let a = &mut v;
        a.push(23);
        println!("The answer is {}", a[3]);
    }
    // ownership is now back with v
    v.push(24);
}

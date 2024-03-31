function Factorial(n: nat): nat
{
    if (n == 0) then 1 else Factorial(n-1)*n
}

method factorial(n: nat) returns (r: nat)
    ensures r == Factorial(n)
{
    r := 1;
    var i := 0;
    while (i != n)
        invariant r == Factorial(i)
        invariant i <= n
        decreases n-i
    {
        i := i + 1;
        r := r * i;
    }
}
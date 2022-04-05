function Factorial(n: nat): nat
{
    if (n == 0) then 1 else Factorial(n-1)*n
}

method factorial(n: nat) returns (y: nat)
    ensures y == Factorial(n)
{
    y := 1;
    var x := n;
    assert y * Factorial(x) == Factorial(n);
    assert x >= 0;
    while (x != 0)
        invariant y * Factorial(x) == Factorial(n);
        decreases x;
    {
        assert (x-1) >= 0;
        assert y * x * Factorial(x-1) == Factorial(n);
        y := y * x;
        x := x - 1;
    }
}
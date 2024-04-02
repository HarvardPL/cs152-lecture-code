function sumTo(i: nat, j: nat): nat
requires i <= j
decreases j
{
    if i==j then 0
    else sumTo(i, j-1) + j
}

method sum(n: nat) returns (r: nat)
ensures r == sumTo(0, n)
{
    var i := 0;
    r := 0;
    while (i < n)
    invariant  0 <= i <= n
    invariant r == sumTo(0, i)
    decreases n-i
    {
      i := i + 1;
      r := r + i;
    }
}
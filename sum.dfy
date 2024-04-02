function sumTo(i: nat, j: nat): nat
requires i <= j
decreases j-i
{
    if i==j then 0
    else i + sumTo(i+1, j)
}

lemma sumToInc(i: nat, j: nat)
requires i <= j
ensures sumTo(i, j) + j == sumTo(i, j+1)
decreases j-i
{
  if i==j
  {
    assert sumTo(i, j+1) == j;
  }
  else
  {
     sumToInc(i+1, j);
  }
}

method sum(n: nat) returns (r: nat)
ensures r == sumTo(0, n)
{
    var i := 0;
    r := 0;
    assert r == sumTo(0, 0);
    while (i < n)
    invariant  0 <= i <= n
    invariant r == sumTo(0, i)
    decreases n-i
    {
        sumToInc(0, i);
        r := r + i;
        i := i + 1;
    }
}
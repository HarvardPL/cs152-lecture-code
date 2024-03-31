// Dafny: https://github.com/dafny-lang/dafny

method ex(bar: nat) returns (baz: int)
    ensures baz == -2 * bar
{
    var foo := 0;
    baz := 0;
    while (foo != bar)
        invariant baz == -2 * foo
        invariant bar >= foo
        decreases bar - foo
    {
        baz := baz - 2;
        foo := foo + 1;
    }
}
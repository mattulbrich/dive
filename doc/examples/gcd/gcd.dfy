method gcd(a: int, b: int) returns (r: int)
    requires  a > 0
    requires b > 0
    ensures exists k:int :: exists l:int :: r == k*a + l*b
{
    var x: int;
    //Init
    r := a;
    x := b;
    while (r != x)
        invariant x > 0
        invariant r > 0
        invariant exists k:int :: exists l:int :: r == k*a + l*b
        decreases  x+r
    {
        if (r > x)
        {
            r := r - x;
        }
        else
        {
            x := x - r;
        }
    }
}

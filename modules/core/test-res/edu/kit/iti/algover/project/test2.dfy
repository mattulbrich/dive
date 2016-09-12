method single(a:int) returns (m:int)
    requires true
    ensures m == a
    decreases 0
{
    m := a;
}
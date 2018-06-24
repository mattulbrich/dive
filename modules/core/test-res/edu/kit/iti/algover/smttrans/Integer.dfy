method negNumber1 (i : int, j: int) returns (k: int)
requires i < 0
requires j > 0
ensures k < i
{
k := i - j;
}

method negNumber2 (i : int, j: int) returns (k: int)
ensures (i > 0) ==> ((-i) < 0)
ensures (i >= 0) ==> ((-i) <= 0)
ensures (-1 * j) == (-j)
{

}

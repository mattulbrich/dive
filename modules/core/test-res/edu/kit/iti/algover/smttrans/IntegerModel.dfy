method negNumberModel (i : int, j: int) returns (k: int)
requires i > 0
ensures k > 0
{
k := i + j;
}

method numberModel (i : int, j: int) returns (k: int)
requires i > 0
requires j > 0
ensures k < i*j
{
k := i + j;
}
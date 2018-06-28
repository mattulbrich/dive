method arrOP (s1: array<int>, s2: array<int>) returns (s3:array<int>)
requires s1[0] > 6
requires s2[0] > 5
ensures s1[0] + s2[0] > 11
ensures s3[0] < 0
ensures s3[1] > 1
{
s3[0] := 4;
s3[1] := 4;
}

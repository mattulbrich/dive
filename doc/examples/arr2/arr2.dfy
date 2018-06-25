method arrOP (s1: array2<int>, s2: array2<int>) returns (s3:array2<int>)
requires s1[0,0] > 6
requires s2[0,0] > 5
requires s1.Length1 > 10
requires s1.Length0 > 5
ensures s1[0,0] + s2[0,0] > 11
ensures s3[1,1] == 0
{
s1[1,1] := 9;
}

method concatSeq (s1: seq<int>, s2: seq<int>) returns (s3:seq<int>)
requires |s1| > 6
requires |s2| > 5
ensures |s1+s2| > 11
{

}

method seqOP2 (s1: seq<int>, s2: seq<int>) returns (s3:seq<int>)
requires |s1| > 2
ensures s1[0] > 3
{
s1[0] := 4;
}

method seqOP3 (s1: seq<int>, s2: seq<int>) returns (sum:int)
requires |s1| > 2
requires s1[0] == 1
requires s1[1] == 2
ensures sum == 3

{
 sum := s1[0] + s1[1];
}

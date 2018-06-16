method seqOP (s1: seq<int>, s2: seq<int>) returns (s3:seq<int>)
requires |s1| > 6 
requires |s2| > 5
ensures |s1+s2| > 4
{
 var s4 := s2;
}

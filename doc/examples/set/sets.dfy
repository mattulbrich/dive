method setOP (s1: set<int>, s2: set<int>) returns (s3:set<int>)
requires |s1| <= 3
requires |s2| >= 5
requires 1 in s1
ensures |s1+s2| > 4
{

}

method intersect(s1: set<int>, s2: set<int>) returns (s3:set<int>)
  requires |s1| > 5
  requires |s2| > 5
  ensures |s1 * s2| < 5
{

}


method setOP2(s1: set<int>, s2: set<int>) returns (s3:set<int>)
  requires |s1| >= 0
  requires |s2| >= 0
  ensures |s1 + s2| >= 0
{

}

method symbexTest(p1:int, p2:array<int>) returns (r1:int, r2:array<int>)
  requires p > 0
  ensures p > 0
  decreases 0
{
  var v1 : int := 0;
  var v1b : int := 0;
  var v2 : array<int>;

  count := 1;
  unmodifiedInLoop := 0;

  while v1 < 0
    invariant true
    decreases 0
  {
    v1 := v1 + 1;
  }

  var v3 : int;
}
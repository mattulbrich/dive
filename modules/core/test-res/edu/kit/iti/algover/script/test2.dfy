// Empty
method m2()
  requires 1 == 3
  ensures 1 == 2
{
  var a: int;
  a := 1;
  while a > 0
    invariant 1 == 4
    decreases 5
  {
  }
}

method foo(x : int) returns (r: int)
  ensures r == 1
{
  r := 1;
}
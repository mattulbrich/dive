class foo
{
var fieldOfClass : int;

method arrayUpdate(a : array<int>, n: int) returns (m : int)
  requires n > 0
  ensures a[0] == m
  ensures a[0] == a[1]
  decreases 0
{

  a[0] := a[1];
  m := a[0];

}

function isValid(a: int, b: int) : bool
{
a + b == b + a
}

}
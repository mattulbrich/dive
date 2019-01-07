method dotdot(a : array<int>, n: int) returns (m : int)
  requires a != null
  ensures a[..] == old(a[..])
  ensures a[0..] == []
  ensures a[..4+5] == []
  ensures a[n*2+3 .. n*3+2] == []
{
  var x := a[..];
  x := x[0..];
  x := x[..4+5];
  x := x[n*2+3 .. n*3+2];
}


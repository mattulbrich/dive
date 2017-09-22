method M(n : int)
{
  var i : int;
  i := 0;
  while i < n
    invariant label I: i<=n
  {
    if i == 5
    {
      i := i + 1;
    }
    i := i + 1;
  }
}
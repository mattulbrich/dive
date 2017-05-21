
method wildcards()
{
  var x: int;
  while *
    invariant true
    decreases 2
  {
    if *
    {
      x := *;
    } else {
      x := *;
    }
  }
}

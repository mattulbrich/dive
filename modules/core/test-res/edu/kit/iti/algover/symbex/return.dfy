method m()
  ensures 1==1
{
  var v : int;

  while v > 0
    invariant v == 42
    decreases v
  {
    if v == 17
    {
      return;
    }
    v := v + 1;
  }

  return;

  v := v + 1;
}

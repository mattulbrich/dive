method symbexTest(p : int)
  ensures unmod == mod
{
  var unmod : int;
  var mod : int;

  unmod := 1;
  mod := unmod;

  mod := *;

  while mod > unmod
    invariant unmod == mod
    decreases unmod+mod
  {
    mod := mod + 1;
  }
}

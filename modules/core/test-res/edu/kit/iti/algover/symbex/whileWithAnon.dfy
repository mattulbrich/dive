class C
{
  var field : int;
  var modset : set<C>;

  method symbexTest(p : int)
    ensures true
    modifies modset
  {
    var unmod : int;
    var mod : int;

    unmod := 1;
    mod := unmod;

    mod := mod + 2;

    while mod > unmod
      invariant unmod == mod
      decreases unmod+mod
    {
      mod := mod + 1;
      field := 1;
    }

    while mod > unmod
      invariant true
      decreases mod
    { }
  }
}

method labelTest(p : int)
  ensures p == -1
  ensures label labelled: p == -2
  ensures p == -3
{

  var p : int;

  while p > 1
    invariant p == 0
    invariant label withLabel: p == 1
    invariant p == 2
    decreases p+count
  {
    count := count + 1;
    assert p == 3;
  }

  assert p == 4;

  if p == 5
  {
    count := 2;
  }
  else
  {
    count := 3;
  }

  assume count > 0;

  // direct initialisation
  var init_direct : int := 42;
  
  if p == count
  {
     count := - count;
  }
  // no else
}
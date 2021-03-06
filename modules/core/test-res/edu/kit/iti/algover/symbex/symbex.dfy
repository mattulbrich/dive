method symbexTest(p : int)
  requires p > 0
  ensures p > 0
  decreases 0
{
  var count : int;
  var unmodifiedInLoop : int;

  count := 1;
  unmodifiedInLoop := 0;

  while p > 1
    invariant p == 2
    decreases p+count
  {
    count := count + 1;
  }

  count := 7;
  assert unmodifiedInLoop == 0;

  if p > 0 
  {
    count := 2;
  }
  else
  {
    count := 3;
  }

  assume count > 0;

  // direct initialisation
  var init_direct : int := 43;
  // without type!
  var init_wo_type := 41;

  if p == count
  {
     count := - count;
  }
  // no else
}
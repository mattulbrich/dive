method labelTest(p : int)
  requires label req_1: collides_with_automatic_numbering
  requires label withReqLabel: p < 0
  requires p == -1
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

  // second loop continues numbering
  // inv collides with automatic naming!
  while true
    invariant label inv_1: p == 4
    invariant label ass_2: p == 5 // nasty collision!
  {
    assert label assert_labelled: p == 6;
    assert p == 7;
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
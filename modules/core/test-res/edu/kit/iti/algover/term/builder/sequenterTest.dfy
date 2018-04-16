method m(p : int, m : set<object>) returns (r:int)
  requires p > 0
  ensures r > 0
  modifies m
  decreases p+1
{
  var local : int;
  local := p;
  if local > 0
  {
     r := local;
  } else {
     r := -local;
  }
}
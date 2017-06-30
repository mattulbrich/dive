method m(p : int) returns (r:int)
  requires p > 0
  ensures r > 0
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
method CallMe(p : int) returns (r : int )
  requires p == 1
  ensures r == 2
{
  r := 2;
}

class Clss {

  method Meth(p : int)
    requires p == 21
    ensures true
  {}
}

method test(c: Clss)
  ensures c == c
{
  var x: int;
  x := CallMe(22);
  
  var y:int := CallMe(23);

  c.Meth(24);
}
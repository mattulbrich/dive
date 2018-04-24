method CallMe(p : int) returns (r : int )
  requires p == 1
  ensures r == 2
{
  r := 2;
}

class Clss {

  var field : int;

  method Meth(p : int)
    requires p == 21
    ensures true
    modifies this
  {
    // not strictly pure:
    field := 42;
  }
}

method test(c: Clss)
  ensures c == c
{
  var x: int;
  x := CallMe(22);
  
  var y:int := CallMe(23);

  c.Meth(24);
}

method recursive(n: int) returns (r: int)
  requires n >= 0
  ensures r == 0
  decreases 2*n
{
  if n == 0
  {
    r := n;
  } else {
    r := recursive(n - 1);
  }
}
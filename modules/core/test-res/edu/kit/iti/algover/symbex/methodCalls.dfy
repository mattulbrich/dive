method CallMe(p : int) returns (r : int )
  requires p == 1
  ensures r == 2
{
  r := 2;
}

method multiReturn() returns (a: int, b:int)
  requires 42 == 42
  ensures a == 1 && b == 2
{
  a := 1;
  b := 2;
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

  x,y := multiReturn();
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

method objectReturn(b: bool) returns (o : Clss)
  ensures true;
{
  if(b)
  {
    o := new Clss;
    o.field := 12;
  } else
  {
    o := objectReturn(true);
  }
}
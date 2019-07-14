method max(x: int, y: int) returns (m: int)
  ensures m > 1
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  m := x;
  if (m < y)
  {
    m := y;
  }
}


function f(a:int):int
{
 a
}

method ff(a: int) returns (b:int)
requires a >= 0 && a < 100
requires a + 1 == a +1 && a>0 ==> b >= 0
ensures a == 1 && f(f(a)) == 2
{}

method simpleConjunction(a: bool, b:bool)
requires a && b
ensures a
{

}





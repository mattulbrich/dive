class foo3
{
var fieldOfClass : int;

method arrayUpdate(a : array<int>, n: int) returns (m : int)
  requires n > 0
  ensures a[0] == m
  ensures a[0] == a[1]
  decreases 0
{

  a[0] := a[1];
  m := a[0];

}

function isValid(a: int, b: int) : bool
{
a + b == b + a
}

method foo(a : int ) returns (b:int)
    requires a > 0
    ensures b >= 0
    decreases 0
{
   if(a >= 5){
    b := a;
   }else{
    b := a-1;
   }

}
}
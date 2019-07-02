
function f2(x : int, y:int) : int {
  x
}

function f1(x : int) : int
  decreases f2(x, 2)
{
  if x == 0 then 0 else 1 + f1(x-1+2)
}

method m1()
  requires f1(3) == 3
{
   while true
     invariant f1(4) == 4
   {
      var i := f1(5);
   }
}

method m2()
{
}
class C {}
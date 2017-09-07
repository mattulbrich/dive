method m(x : int, a : array<int>) returns (r : int) 
   ensures r > 0
{

   var i : int;

   i := x;
   i := i + 2;
   i := a[i];
   r := i;

 }
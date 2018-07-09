function fib(n: int): int
  requires n >= 0
//  decreases n
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}


method ComputeFib(n: int) returns (b: int)
requires n >= 0
   ensures b == fib(n)
{
   if n == 0
   {
     b := 0;
   } else
   {


   var i: int := 1;
   var a := 0;
       b := 1;
   while i < n

    invariant 0 < i <= n
    invariant a == fib(i - 1)
    invariant b == fib(i)
    decreases n -i

   {
     var c := a;
      a := b;
      b := c+b;
      i := i + 1;
   }
}
}

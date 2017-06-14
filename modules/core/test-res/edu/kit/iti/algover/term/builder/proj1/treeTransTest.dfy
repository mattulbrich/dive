method m(i1 : int) returns (i2:int)
   ensures i2 > 0
{
   var x: int; 

   x := 5;
   x := i1 + x;
   i2 := i1 * 2;
}

class D {
   var field : D;
}

class C {

   var field : int;

   method n(d: D, i1 : int) 
     ensures field > 0
   {
      field := field + 1;
      d.field := null;
   }
}

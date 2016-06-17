method runtimeChecks()
{
   var a:array<int>;
   var y:int;
   var x:int;
   var b:bool;

   x := a[y];
   b := y > 0 || a[y] > 0;
 }
 
 method runtimeInIf()
 {
   var a:array<int>;
   var i:int;

   if(i>0 && 5+a[i] > 0) 
   {} else {}
 }

 method runtimeInWhile()
 {
   var a:array<int>;
   var i:int;

   while(i>0 ==> a[i]-i > 0) 
     invariant i>2
     decreases i
   { i := i + 1; }
 }
/* Was a bug in the parser */

class C
{
  var x: C;
  
  method m()
  {
     x.x.x := x.x.x;
  }
}
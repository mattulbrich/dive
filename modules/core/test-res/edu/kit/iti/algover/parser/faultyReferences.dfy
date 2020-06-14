
/*
 * This should not be parseable for various reasons.
 */

class D {
   var df: int;

   method md(c : C)
   {
      c.cf := c.df;
      c.df := c.cf;

      c.mc(c);
      c.md(c);
   }
}

class C {
   var cf: int;

   method mc(d : D)
   {
      d.cf := d.df;
      d.df := d.cf;

      d.mc(d);
      d.md(d);
   }
}

class ArrayProblems
{
   method m()
   {
      var a : Unknown;

      a.f := 0;
   }
}

class IllegalVariableRefs
{
   method m()
      ensures local == 0
   {
      var local : int;
   }
}

method self()
{
   // was responsible for a stackoverflow
   var y:= y;
}
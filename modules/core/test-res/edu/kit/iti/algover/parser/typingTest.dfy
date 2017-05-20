class C
{
   var intfield : int;
   var cfield : C;

   method testAssignments()
   {
      var i_var : int;
      var b_var : bool;
      var c_var : C;

      i_var := 0;
      i_var := i_var + i_var;
      i_var := i_var * i_var;
     // i_var := i_var / i_var;
      b_var := i_var < 0;
      c_var := this;
      c_var := cfield;
      c_var := this.cfield;
      c_var := this.cfield.cfield;
      i_var := intfield;
   }

   method testWildcards()
   {
      var i_var : int;
      var b_var : bool;
      var c_var : C;

      i_var := *;
      b_var := *;
      c_var := *;

      if *
      { }

      while *
      { }
   }

   method testControl()
   {
      var i : int;

      if i > 0
      {
         i := i + 1;
      }
      else
      {
         i := i + 1;
      }

      while i > 0
      {
         i := i + 1;
      }
   }
}
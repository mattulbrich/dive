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

      c_var := null;
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

      if i == 0
      { }
   }

   method testContracts()
     requires true
     ensures true
     // modifies this
     decreases 2
   {
     while true
       invariant false
       // modifies this
       decreases 2
     {
     }
   }

   method testInitialisation()
   {
     var i : int := 22;
     var c : C := null;
   }

   method testNull()
   {
     var c : C;

     c := null;
     if null == null
     { }
     if c == null
     { }
     if c != null
     { }
     while null == c
     { }
   }

   method testOps()
   {
      var b : bool;
      var i : int;

      b := 1 < 2;
      b := 1 <= 2;
      b := 1 > 2;
      b := 1 >= 2;

      i := 1 + 1;
      i := 1 - 1;
      i := 1 * 1;
      // i := 1 / 1;
   }

   method arrays() {
      var a : array<int>;
      var i : int;
      var c : C;

      i := a[0];
      a[0] := i;

      a[0] := null;
      c := a[0];
   }

   method failAssignments()
   {
      var i : int;
      var c : C;

      i := 0;
      i := null;
      i := c;
      i := true;

      c := 0;
      c := null;
      c := i;
      c := true;

      var localVar1 : int := null;
      var localVar2 : C := 0;
   }

}

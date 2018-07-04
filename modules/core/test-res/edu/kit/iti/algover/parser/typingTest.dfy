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

      label if_label: if *
      { }

      while *
      { }

      label while_label: while *
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

   method sequenceTest(s1 : seq<int>)
   {
      var s2 : seq<int>;

      s2 := s1;
      s2[0] := 0;
      s1[1] := s2[1];
   }

   method quantifiers()
     ensures forall i : int :: i == i
     ensures exists x : int :: x == 0
     ensures let x,y := 1,true :: y && x > 0
   {}

   method varDecls() returns (ret_r : int)
   {
     var l_i : int;
     var l_x1, l_x2 : int;
     var l_y : int := 42;
     var l_v := 44;

     ret_r := l_i+l_x1+l_x2+l_y+l_v;
   }

   method multiReturn() returns (a:int, b:int)
   {
     multiReturn();
   }
}

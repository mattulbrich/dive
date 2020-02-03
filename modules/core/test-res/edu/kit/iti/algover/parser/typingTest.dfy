class C
{
   var intfield : int;
   var cfield : C;

   method testAssignments()
   {
      var i_var : int;
      var b_var : bool;
      var c_var : C;
      var o_var : object;
      var a_var : array<int>;
      var seqC_var : seq<C>;
      var seqO_var : seq<object>;
      var setC_var : set<C>;
      var setO_var : set<object>;

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

      o_var := c_var;
      o_var := null;
      o_var := a_var;
      seqO_var := seqC_var;
      setO_var := setC_var;
      // see also testIllegalRefAssignment
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
     ensures old(intfield) == intfield
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
      i := 1 / 1;
      i := i % 2;
   }

   // this fails!
   method arrays() {
      var a : array<int>;
      var a2 : array2<int>;
      var i : int;
      var c : C;

      i := a[0];
      a[0] := i;

      a[0] := null;
      c := a[0];

      i := a[0,0];
      i := a2[0];
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

      var l := |s1|;
   }

   method quantifiers()
     ensures forall i : int :: i == i
     ensures exists x : int :: x == 0
     ensures (forall i : int :: i == i) <==> (exists i : int :: i == 0)
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

   method setTest(s1 : set<int>, a : array<int>)
     modifies { this, a }
   {
     var s2 := { 1, 2, 3 };
    // var s3 := { 1 } + { 2 };
   }

   method arrays2() {
     var a : array2<int>;
     var i : int;
     var j : int;

     i := a[0, 0];
     a[i, j] := i;

     i := a.Length0;
     j := a.Length1;
   }

   // this fails!
   method illegalModifies(o: object)
      modifies 1+1, o
   {}

   function fct(i: int) : int {0}

   method functionReference()
     requires fct(0) == 0
   { var r := this.fct(0) + cfield.fct(0) + fct(0); }

   method dotdots(s: seq<int>, a: array<int>)
     requires s == a[..]
     ensures s[0..] == s[..1] == s[0..1];
   { }

   method extensions(l: seq<int>, s: set<int>)
     requires l == [1,2,3]
     requires s == {1,2,3}
     ensures l != []
     ensures [] == []
     ensures s != {}
     ensures {} == {}
   {
     var o: object;
     assert {o, this} == {this, o};
   }

   method testAssertAssume()
   {
     assume 1==0;
     assert 1==2;
   }

   method testIllegalRefAssignment(o: object, seqO: seq<object>, setO: set<object>)
   {
      var c: C;
      var a: array<int>;
      var seqC: seq<C>;
      var setC: set<C>;

      c := o;
      c := a;
      setC := setO;
      seqC := seqO;
   }

   method multiReturnObject() returns (a:object, c:C)
   {}

   method assignObjectTuples()
   {
      var x: object;
      var c: C;
      var y: object;

      x,c := multiReturnObject();
      x,y := multiReturnObject();
   }

   method assignObjectTuplesFail()
   {
      var x: object;
      var c: C;

      c,x := multiReturnObject();
   }

   method additions()
   {
      var sq : seq<int>;
      var st : set<int>;

      assert sq + sq + [1] == sq;
      assert 1 + 1  == 2;
      assert st + st + {1} == st;
   }

   method challengeNull()
   {
      var setC: set<C>;
      setC := { null };
   }

   method testMaps()
   {
      var m: map<int, bool>;
      m := map[];
      m := map[5:=true];
      m := m[3:=false];

      var om: map<object, object>;
      om := map[null := null];
      om := om[this := null];
      om := om[null := this];

      var d: D;
      var widenedMap := map[d := this][this := d];
      var widenedMap2 := map[d := this, this := d];
   }

   method mapExFail1()
   {
      var m := map[1 := 2][true := 3];
   }

   method mapExFail2()
   {
      var m := map[1 := 2, true := 3];
   }
}

class D {}

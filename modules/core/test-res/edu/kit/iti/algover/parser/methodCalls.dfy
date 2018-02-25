class C
{
   method m(i : int) returns (r : int)
   {
      var c : C := new C;
      c := new C;
      c := new C.m(42);

      m(54);
      r := m(48);
      r := this.m(22);
      c.m(33);
   }
}
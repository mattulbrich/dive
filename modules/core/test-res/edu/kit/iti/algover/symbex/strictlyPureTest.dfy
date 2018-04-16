class C {

  var field : int;
  
  method pure1(x: int) returns (y: int)
  {
    y := 0;
  }

  method nonpure2()
  {
    field := 0;
  }

  method nonpure3(a: array<int>)
  {
    a[0] := 0;
  }

  method pure4() {
//    pure1(22);
    pure4();
  }

  method nonpure5() {
    nonpure2();
    nonpure5();
  }

}

method indirect1(c : C)
{
  c.nonpure2();
}

method indirect2(c : C)
{
  indirect1(c);
}

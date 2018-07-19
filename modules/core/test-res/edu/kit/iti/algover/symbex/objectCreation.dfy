class C {

  method Init(p : int)
    requires p == 1
    ensures this == this
  {}

  method Init2() returns (r: int)
    requires 1 == 1
    ensures this == this
  {}

}

method test()
  ensures label ens: true
{
  var c: C;
  c := new C;
  c := new C.Init(23);

  var c2:C := new C.Init(42);

  var c3 := new C.Init2();

  var c4 := new C[10];
  var c5 : array<int>;
  c5 := new int[c4.Length];
}
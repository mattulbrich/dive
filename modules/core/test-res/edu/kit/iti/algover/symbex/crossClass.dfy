class C {
  var d : D;

  method setD(x : D)
    requires x != null
    ensures d == x
    ensures x.c == this
    modifies this, x
  {
    this.d := x;
    d := x;
    x.c := this;
  }
}

class D {
  var c : C;
}

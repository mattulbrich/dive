class C {

  method Init(i : int) {}

  method m() {
    var c := new C;
    var c2 : C := new C;
    var c3 := new C.Init(42);

    c := new C;
    c2 := new C.Init(44);
  }
}
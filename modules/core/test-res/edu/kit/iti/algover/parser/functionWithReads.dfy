class C {
  var x: int;
  
  function f() : int
    requires true
    reads this
  {
    this.x + 1
  }
}

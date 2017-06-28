method m(i1 : int) returns (i2:int)
  ensures i2 > 0
{
    var x: int; x := 5;
    x := i1 + x;
    i2 := i1 * 2;
}

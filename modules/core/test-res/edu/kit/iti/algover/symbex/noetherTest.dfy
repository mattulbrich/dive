method noetherTest(a: int, b: int) returns (r: int)
  requires a >= 0
  requires b >= 0
{

    var x := a;
    var y := b;

    while x >= 0 && y >= 0
      decreases y, x
    {
        if x < y
        {
            var t: int;
            t := x;
            x := y;
            y := t;
        }
        else
        {
            x := x - 1;
        }
    }
    r := x;
}
method noetherTest(a: int, b: int) returns (r: int)
  requires a >= 0
  requires b >= 0
{

    while a >= 0 && b >= 0
      decreases b, a
    {
        if a < b 
        {
            var t: int;
            t := a;
            a := b;
            b := t;
        }
        else
        {
            a := a - 1;
        }
    }
    r := a;
}
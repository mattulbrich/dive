method max(x: int, y: int) returns (m: int)
  ensures m >= x && m >= y
  ensures m == x || m == y
{
  m := x;
  if m < y
  {
    m := y;
  }
}

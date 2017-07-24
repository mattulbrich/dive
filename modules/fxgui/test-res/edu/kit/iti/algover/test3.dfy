// Empty
method m3() { }

method x(x : int)
  ensures 1 == 1 + 3 + 5 + 2 + 3 && 6 > 4 && 4 * 1 < 3
{
  x := 1;
}

// Empty
method m3() { }

method x(x : int)
  ensures 1 == 2 && 2 == 3 && 4 == 5
  ensures 5==5 && 6==6
{
  x := 1;
}
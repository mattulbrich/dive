
// Does this test file make sense at all?

// Empty
method m3() { }

method x()
  ensures 1 == 2 && 2 == 3 && 4 == 5
  ensures 5==5 && 6==6
{
  var x := 1;
}
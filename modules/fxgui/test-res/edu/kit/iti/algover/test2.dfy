// Empty
method m2(a: int) 
  requires 1 == 3
  ensures 1 == 2
{ 
  while a > 0
    invariant 1 == 4
    decreases 5
  {
  }
}

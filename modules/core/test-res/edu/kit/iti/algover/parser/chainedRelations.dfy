lemma m(x: int, y:int, z:int)
  requires x == y == z // 0
  requires x > y >= z // 1
  requires x > y == z // 2
  requires x == y >= z // 3
  requires (x > 0) == true // 4
  requires (x == 0) == true // 5
  requires (x+1) < (x+2) < (x+3) // 6
{ }
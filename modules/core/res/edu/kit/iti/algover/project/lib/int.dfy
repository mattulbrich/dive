/* TODO HEADER */


lemma plus_0(a : int)
  ensures a + 0 == a
{}

lemma plus_0x(a : int)
  ensures 0 + a  == a
{}

lemma times_1(a: int)
  ensures a * 1 == a
{}

lemma times_1x(a: int)
  ensures 1 * a == a
{}

lemma times_0(a: int)
  ensures a * 0 == 0
{}

lemma times_0x(a:int)
  ensures 0 * a == 0
{}

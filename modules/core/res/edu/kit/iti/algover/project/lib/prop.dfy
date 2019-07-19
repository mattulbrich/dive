
/* TODO HEADER */
  

lemma and_true(a: bool)
  ensures (a && true) == a
{}

lemma and_true_x(a: bool)
  ensures (true && a) == a
{}

lemma and_false(a: bool)
  ensures (a && false) == false
{}

lemma and_false_x(a: bool)
  ensures (false && a) == false
{}

lemma or_false(a: bool)
  ensures (a || false) == a
{}

lemma or_false_x(a: bool)
  ensures (false || a) == a
{}

lemma or_true(a: bool)
  ensures (a || true) == true
{}

lemma or_true_x(a: bool)
  ensures (true || a) == true
{}

lemma imp_true(a: bool)
  ensures (a ==> true) == true
{}

lemma imp_true_x(a: bool)
  ensures (true ==> a) == a
{}

lemma imp_false(a: bool)
  ensures (a ==> false) == (!a)
{}

lemma imp_false_x(a: bool)
  ensures (false ==> a) == true
{}

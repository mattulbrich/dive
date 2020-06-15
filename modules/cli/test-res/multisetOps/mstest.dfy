method Main() {
  var ms: multiset<int>;
  ms := multiset([6,5,4,4,2,1]);

  assert (ms[6] == 1);
  assert (ms[4] == 2);
  assert (ms[42] == 0);

  assert forall k :: k !in ms ==> ms[k] == 0;
  
  print(ms[4]);
}
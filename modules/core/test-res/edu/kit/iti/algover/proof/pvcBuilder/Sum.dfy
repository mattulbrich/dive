function Sum(a: seq<int>, s: int, t: int): int
  requires 0 <= s <= t <= |a|
{
  if s == t then 0 else Sum(a, s, t-1) + a[t-1]
}

method MaxSegSum(a: seq<int>) returns (k: int, m: int)
  ensures 0 <= k <= m <= |a|
  ensures forall p,q :: 0 <= p <= q <= |a| ==> Sum(a, p, q) <= Sum(a, k, m)
{
  k := 0;
  m := 0;
  var s := 0;  // invariant s == Sum(a, k, m)
  var n := 0;
  var c := 0;  // invariant t == Sum(a, c, n)
  var t := 0;
  while (n < |a|)
    invariant 0 <= c <= n <= |a| && t == Sum(a, c, n)
    invariant forall b :: 0 <= b <= n ==> Sum(a, b, n) <= Sum(a, c, n)
    invariant 0 <= k <= m <= n && s == Sum(a, k, m)
    invariant forall p,q :: 0 <= p <= q <= n ==> Sum(a, p, q) <= Sum(a, k, m)
  {
    t := t + a[n];
    n := n + 1;
    if (t < 0) {
      c := n;
      t := 0;
    } else if (s < t) {
      k := c;
      m := n;
      s := t;
    }
  }
}

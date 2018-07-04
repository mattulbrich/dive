method Cubes(a: array<int>)
  ensures forall i :: 0 <= i < a.Length ==> a[i] == i*i*i

{
  var n := 0;
  var c := 0;
  var k := 1;
  var m := 6;
  while n < a.Length
    invariant 0 <= n <= a.Length
    invariant forall i :: 0 <= i < n ==> a[i] == i*i*i
    invariant c == n*n*n
    invariant k == 3*n*n + 3*n + 1
    invariant m == 6*n + 6
  {
    a[n] := c;
    c := c + k;
    k := k + m;
    m := m + 6;
    n := n + 1;
  }
}
/**
method FindZero(a: array<int>) returns (r: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 <= i && i+1 < a.Length ==> a[i]-1 <= a[i+1]
  ensures 0 <= r ==> r < a.Length && a[r] == 0
  ensures forall i :: 0 <= i < a.Length ==> r < 0 ==>  a[i] != 0
{
  var n := 0;
  while (n < a.Length)
    invariant forall i :: 0 <= i < n && i < a.Length ==> a[i] != 0
  {
    if (a[n] == 0) { r := n; return; }
    Lemma(a, n, a[n]);
    n := n + a[n];
  }
  r := -1;
}

lemma Lemma(a: array<int>, k: int, m: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 <= i && i+1 < a.Length ==> a[i]-1 <= a[i+1]
  requires 0 <= k
  requires k < a.Length ==> m <= a[k]
  ensures forall i :: k <= i < k+m && i < a.Length ==> a[i] != 0
  decreases m
{
  if (0 < m && k < a.Length) {
    assert a[k] != 0;
    Lemma(a, k+1, m-1);
  }
}


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
**/

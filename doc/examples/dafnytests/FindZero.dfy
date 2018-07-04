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

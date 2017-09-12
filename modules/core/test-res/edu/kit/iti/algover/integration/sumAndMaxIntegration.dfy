
method M(N: int, a: array<int>) returns (sum: int, max: int)
  requires 0 <= N && a != null && a.Length == N && (forall k : int :: 0 <= k && k < N ==> 0 <= a[k])
  ensures label sumLessEqNMax: sum <= N * max
{
  sum := 0;
  max := 0;
  var i : int := 0;
  while (i < N)
    invariant label bounds: 0 <= i && i <= N 
    invariant label sumMax: sum <= i * max
    decreases N - i
  {
    if max < a[i]
    {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

method sumAndMax(a: seq<int>) returns (sum: int, max: int)
  requires a.Length >= 1
  ensures forall i: int :: 0 <= i && i < a.Length ==> a[i] <= max
  ensures a.Length * max >= sum
{
  print "hallo";
  sum := a[0];
  max := a[0];

  var i: int := 1;
  while (i < a.Length)
    invariant 0 <= i && i <= a.Length
    invariant forall k: int :: 0 <= k && k < i ==> a[k] <= max
    invariant i * max >= sum
    decreases a.Length - i
  {
    if (a[i] > max)
    {
      max := a[i];
    }
    sum := sum + a[i];
    i := i + 1;
  }
}

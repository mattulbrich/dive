// GOAL: Know how to parse
//   https://github.com/Microsoft/dafny/blob/master/Test/vstte2012/Two-Way-Sort.dfy


// method swap<T>(a: array<T>, i: int, j: int)
method swap(a: array<bool>, i: int, j: int)
  requires a != null
  // requires 0 <= i < j < a.Length
  requires 0 <= i && i < j && j < a.Length
  ensures a[i] == old(a[j])
  ensures a[j] == old(a[i])
  // ensures forall m :: 0 <= m < a.Length && m != i && m != j ==> a[m] == old(a[m]);
  ensures (forall m:int :: 0 <= m && m < a.Length && m != i && m != j ==> a[m] == old(a[m]))
  // ensures multiset(a[..]) == old(multiset(a[..]));
  modifies a
{
  var t:bool := a[i];
  a[i] := a[j];
  a[j] := t;
}

method two_way_sort(a: array<bool>)
  requires a != null
  // ensures forall m,n :: 0 <= m < n < a.Length ==> (!a[m] || a[n])
  ensures (forall m:int :: (forall n:int :: 0 <= m && m < n && n < a.Length ==> (!a[m] || a[n])))
  // ensures multiset(a[..]) == old(multiset(a[..]));
  modifies a
{
  var i:int := 0;
  var j:int := a.Length - 1;
  while (i <= j)
    // invariant 0 <= i <= j + 1 <= a.Length;
    invariant 0 <= i && i <= j + 1 && j+1 <= a.Length
    invariant (forall m:int :: 0 <= m && m < i ==> !a[m])
    invariant (forall n:int :: j < n && n < a.Length ==> a[n])
    // invariant multiset(a[..]) == old(multiset(a[..]))
  {
    if (!a[i]) {
      i := i+1;
    } else { if (a[j]) {
      j := j-1;
    } else {
      swap(a, i, j);
      i := i+1;
      j := j-1;
    }}
  }
}
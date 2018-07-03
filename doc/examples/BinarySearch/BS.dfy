method BinarySearch(a: array<int>, key: int) returns (r: int)
  requires forall i,j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
  ensures 0 <= r ==> r < a.Length && a[r] == key
  ensures forall k: int :: 0 <= k < a.Length ==> r < 0 ==> a[k] != key
{
  var lo := 0;
  var hi := a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant forall k: int :: 0 <= k < lo ==> a[k] != key
    invariant forall k: int :: hi <= k < a.Length ==> a[k] != key
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if key < a[mid] {
      hi := mid;
    } else if a[mid] < key {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}

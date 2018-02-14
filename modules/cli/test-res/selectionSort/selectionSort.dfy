method selectionSort(a: seq<int>) returns (r: seq<int>)
  ensures forall i: int :: forall j:int ::
       0 <= i < j < r.Length ==> r[i] <= r[j]
//  ensures asBag(a) == asBag(r)
{
  r := a;
  
  var x: int := 0;
  while x < r.Length - 1
    invariant label xInBounds: 0 <= x <= r.Length
    invariant label sorted: forall i: int :: forall j:int ::
       0 <= i < j < x ==> r[i] <= r[j]
    invariant label above: x == 0 ||
          (forall k:int :: x <= k < r.Length ==> r[x-1] <= r[k])
//     invariant label bag: asBag(a) == asBag(r)
    decreases r.Length - x
  {

    var y: int := x+1;
    var m: int := y;
    while y < r.Length
      invariant x < y <= r.Length
      invariant x < m <= y && m < r.Length
      invariant forall l: int :: x <= l < y ==> r[l] <= r[m]
//      invariant asBag(a) == asBag(r)
    decreases r.Length - y
    {
      if a[y] > a[m]
      {
        m := y;
      }
      y := y + 1;
    }
    var t:int := a[m];
    a[m] := a[x];
    a[x] := t;

    x := x + 1;
  }
}

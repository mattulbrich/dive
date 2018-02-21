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

    var y: int := x;
    var m: int := x;
    while y < r.Length
      invariant label yInBounds: x <= y <= r.Length
      invariant label mInBounds: x <= m <= y && m < r.Length
      invariant label mIsMin: forall l: int :: x <= l < y ==> r[m] <= r[l]
//      invariant asBag(a) == asBag(r)
    decreases r.Length - y
    {
      if a[y] < a[m]
      {
        m := y;
      }
      y := y + 1;
    }
    var t:int := r[m];
    r[m] := r[x];
    r[x] := t;
    // assert r[x] <= r[x+1];

    x := x + 1;
    // assert r[x-1] <= r[x];
  }
}


settings {
  "Default Script" = "boogie;"
}

method selectionSort(a: seq<int>) returns (r: seq<int>)
  ensures forall i: int :: forall j:int ::
       0 <= i < j < |r| ==> r[i] <= r[j]
  ensures multiset(a) == multiset(r)
{
  r := a;
  
  var x: int := 0;
  while x < |r| - 1
    invariant label xInBounds: 0 <= x <= |r|
    invariant label sorted: forall i: int :: forall j:int ::
       0 <= i < j < x ==> r[i] <= r[j]
    invariant label above: x == 0 ||
          (forall k:int :: x <= k < |r| ==> r[x-1] <= r[k])
    invariant multiset(a) == multiset(r)
    decreases |r| - x
  {

    var y: int := x;
    var m: int := x;
    while y < |r|
      invariant label yInBounds: x <= y <= |r|
      invariant label mInBounds: x <= m <= y && m < |r|
      invariant label mIsMin: forall l: int :: x <= l < y ==> r[m] <= r[l]
      invariant multiset(a) == multiset(r)
    decreases |r| - y
    {
      if r[y] < r[m]
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

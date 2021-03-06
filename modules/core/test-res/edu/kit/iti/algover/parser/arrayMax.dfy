method max(a : array<int>, n: int) returns (m : int)
  requires n > 0
  // this also tests "|" in quantifiers
  ensures label greater: (forall i | 0 <= i && i < n :: a[m] >= a[i])
  ensures label witness: (exists i : int | 0 <= i && i < n :: a[m] == a[i])
  decreases 0
{

  assume n == a.Length;

  var i:int := 0;
  
  m := 0;
  
  label mainLoop: while i < n
    invariant label inbounds: 0 <= i && i <= n
    invariant label greater: (forall j:int :: 0 <= j && j < i ==> a[m] >= a[j])
    invariant label witness: m == 0 || (exists j:int :: 0 <= j && j < i && a[m] == a[j])
    invariant label witness_in_bounds: 0 <= m && m < n
    decreases n - i
  {
    if (a[i] > a[m])
    {
      m := i;
    }
    i := i+1;
  }
}



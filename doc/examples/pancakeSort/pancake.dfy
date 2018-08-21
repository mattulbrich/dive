

// 15 min
method flip(input: seq<int>, bound: int) returns (a: seq<int>)
  requires 0 <= bound < input.Length
  ensures forall i :: 0 <= i <= bound ==> a[i] == input[bound-i]
  ensures forall i :: bound < i < a.Length ==> a[i] == input[i]
  ensures |a| == |input|
//  ensures multiset(a[..]) == old(multiset(a[..]))
{
  a := input;
  if bound == 0
  {
    return ;
  }

  var i := 0;

  while(2*i < bound)
    invariant 0 <= 2*i <= bound+1
    invariant bound > 0
    invariant forall j :: 0 <= j < i ==> a[bound - j] == input[j] && a[j] == input[bound - j]
    invariant forall j :: i <= j <= bound-i ==> a[j] == input[j]
    invariant forall j :: bound < j < a.Length ==> a[j] == input[j]
    invariant |a| == |input|
//    invariant multiset(a[..]) == old(multiset(a[..]))    
    decreases bound-2*i+1
{
    var aux := a[bound - i];
    a[bound - i] := a[i];
    a[i] := aux;
    i := i + 1;
  }
      
}

// 7 min
method maxIndex(a: seq<int>, bottom: int) returns (localIndex: int)
  requires 0 < bottom < a.Length
  ensures 0 <= localIndex <= bottom
  ensures forall i :: 0 <= i <= bottom ==> a[i] <= a[localIndex]
  // ensures multiset(a[..]) == old(multiset(a[..]))
{
  localIndex := bottom;

  var k := bottom-1;
  while k >= 0
    invariant k >= -1
    invariant bottom >= localIndex
    invariant localIndex >= k+1
    invariant forall j :: k < j <= bottom ==> a[j] <= a[localIndex]
    decreases k+1
  {
    if a[k] > a[localIndex]
    {
      localIndex := k;
    }
    k := k - 1;
  }
}


// 11 min
method sort(input: seq<int>) returns (a: seq<int>)
  requires input.Length > 1
  ensures forall i :: 0 <= i < a.Length -1 ==> a[i] <= a[i+1];
  // ensures multiset(a[..]) == old(multiset(a[..]))
{
  a := input;
  var k := a.Length - 1;
  while k > 0
    invariant label kInBounds: 0 <= k < a.Length
    invariant label sorted: forall j :: k <= j < a.Length - 1 ==> a[j] <= a[j+1]
    invariant label unsorted: k < a.Length - 1 ==> forall i :: 0 <= i <= k ==> a[i] <= a[k+1]
    // invariant multiset(a[..]) == old(multiset(a[..]))
  decreases k
  {
    var flipbound := maxIndex(a, k);

    if 0 < flipbound < k
    {
      a:= flip(a, flipbound);
    }

    if flipbound < k
    {
      a:= flip(a, k);
    }

    k := k - 1;
  }

}
    


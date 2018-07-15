

// 15 min
method flip(a: array<int>, bound: int)
  requires a != null
  requires 0 <= bound < a.Length
  ensures forall i :: 0 <= i <= bound ==> a[i] == old(a[bound-i])
  ensures forall i :: bound < i < a.Length ==> a[i] == old(a[i])
//  ensures multiset(a[..]) == old(multiset(a[..]))
  modifies {a}
{

  if bound == 0
  {
    return;
  }

  var i := 0;

  while(2*i < bound)
    invariant 0 <= 2*i <= bound+1
    invariant bound > 0
    invariant forall j :: 0 <= j < i ==> a[bound - j] == old(a[j]) && a[j] == old(a[bound - j])
    invariant forall j :: i <= j <= bound-i ==> a[j] == old(a[j])
    invariant forall j :: bound < j < a.Length ==> a[j] == old(a[j])
//    invariant multiset(a[..]) == old(multiset(a[..]))    
  {
    var aux := a[bound - i];
    a[bound - i] := a[i];
    a[i] := aux;
    i := i + 1;
  }
      
}

// 7 min
method maxIndex(a: array<int>, bottom: int) returns (localIndex: int)
  requires a != null
  requires 0 < bottom < a.Length
  ensures 0 <= localIndex <= bottom
  ensures forall i :: 0 <= i <= bottom ==> a[i] <= a[localIndex]
  // ensures multiset(a[..]) == old(multiset(a[..]))
{
  localIndex := bottom;

  var k := bottom-1;
  while k >= 0
    invariant bottom >= localIndex
    invariant localIndex >= k+1
    invariant forall j :: k < j <= bottom ==> a[j] <= a[localIndex]
  {
    if a[k] > a[localIndex]
    {
      localIndex := k;
    }
    k := k - 1;
  }
}


// 11 min
method sort(a: array<int>)
  requires a != null && a.Length > 1
  ensures forall i :: 0 <= i < a.Length -1 ==> a[i] <= a[i+1];
  // ensures multiset(a[..]) == old(multiset(a[..]))
  modifies {a}
{

  var k := a.Length - 1;
  while k > 0
    invariant 0 <= k < a.Length
    invariant forall j :: k <= j < a.Length - 1 ==> a[j] <= a[j+1]
    invariant k < a.Length - 1 ==> forall i :: 0 <= i <= k ==> a[i] <= a[k+1]
    // invariant multiset(a[..]) == old(multiset(a[..]))
  {
    var flipbound := maxIndex(a, k);

    if 0 < flipbound < k
    {
      flip(a, flipbound);
    }

    if flipbound < k
    {
      flip(a, k);
    }

    k := k - 1;
  }

}
    

method Main()
{

  var a := new int[10];
  a[0] := 9;
  a[1] := 3;
  a[2] := 8;
  a[3] := 2;
  a[4] := 7;
  a[5] := 4;
  a[6] := 0;
  a[7] := 1;
  a[8] := 5;
  a[9] := 6;

  sort(a);

  print(a);

  var i := 0;
  while i < a.Length
  {
    print(a[i]);
    print(" ");
    i := i + 1;
  }
}

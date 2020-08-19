// ---- Automatically generated settings ----
//> settings {
//>    "KeY Timeout" = "10",
//>    "Dafny Timeout" = "5",
//>    "SMT Timeout" = "10",
//>    "Sequent Generation Type" = "ass-simp"
//> }
// ---- End of settings ----

function IsSortedBetween(a: array<int>, lo: int, hi: int): bool
  requires a != null
  requires 0 <= lo <= hi <= a.Length
  reads a
{
  forall k, l :: lo <= k < l < hi ==> a[k] <= a[l]
}

function IsSorted(a: array<int>): bool
  requires a != null
  reads a
{
  IsSortedBetween(a, 0, a.Length)
}


function IsPermutation(a1: array<int>, a2: array<int>): bool
  requires a1 != null
  requires a2 != null  
  reads a1
  reads a2
{
  multiset(a1[..]) == multiset(a2[..])
}


// as seen in
// "A Tutorial on Using Dafny to Construct Verified Software"
// by Paqui Lucio
// doi:10.4204/EPTCS.237.1

method BubbleSort (a: array<int>)
  requires a != null
  modifies a
  ensures IsSorted(a)
  ensures IsPermutation(a, old(a))
{
  if (a.Length <= 1) {
    return;
  }
  var i := 1;
  while (i < a.Length) 
    decreases a.Length - i
    invariant 1 <= i <= a.Length
    invariant IsSortedBetween(a, 0, i)
    invariant IsPermutation(a, old(a))
  {
    BubbleStep(a, i);
    i := i + 1;
  }
}

method BubbleStep(a: array<int>, i: int)
  requires a != null
  requires 0 <= i < a.Length
  requires IsSortedBetween(a, 0, i)
  modifies a
  ensures IsSortedBetween(a, 0, i + 1)
  ensures IsPermutation(a, old(a))
{
  var j := i;
  while (j > 0 && a[j-1] > a[j])
    decreases j
    invariant 0 <= j <= i
    invariant IsSortedBetween(a, 0, j)
    invariant IsSortedBetween(a, j, i + 1)
    invariant 1 < j + 1 <= i ==> a[j-1] <= a[j+1]
    invariant IsPermutation(a, old(a))
  {
    Swap(a, j - 1, j);
    j := j - 1;
  }
}


method Swap(a: array<int>, i: int, j: int)
  requires a != null
  requires 0 <= i < a.Length
  requires 0 <= j < a.Length
  modifies a  
  ensures a.Length == old(a).Length
  // ensure elements i and j are swapped
  ensures a[i] == old(a[j]) && a[j] == old(a[i])
  // ensure all others umodified
  ensures forall k :: ((0 <= k < a.Length) && k != i && k != j) ==> a[k] == old(a[k])
  // ensure permutation of old array  
  ensures IsPermutation(a, old(a))
  
{
  var tmp := a[i];
  assert tmp == old(a[i]);
  a[i] := a[j];
  a[j] := tmp;
  assert a[i] == old(a[j]);
  assert a[j] == old(a[i]);
}

include "file.dfy"
//\\ include "file2.dfy"
include "free.dfy" //\\ for free
//\\ include "free2.dfy" for free

//\\ settings {
//\\   // That is the way in which sequents are generated
//\\   Sequenter = default
//\\   SMT_Timeout = 200
//\\   AutoSnapshot = 1800
//\\   ProofsFile = "otherFilename.proofs"
//\\ }

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

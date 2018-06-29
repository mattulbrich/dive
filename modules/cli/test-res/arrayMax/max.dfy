method getMax(s : seq<int>) returns (max : int)
  requires |s| > 0
  ensures forall k | 0 <= k < |s| :: s [ k ] <= max
{
  var i := 0;
  max := s[0];
  while i < |s|
    invariant 0 <= i <= |s|
    invariant forall a : int | 0 <= a < i :: s [ a ] <= max
    decreases |s| - i
  {
    if s [ i ] > max
    {
      max := s [ i ];
    }
    i := i + 1;
  }
}

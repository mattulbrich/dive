method getMax(s : seq<int>) returns (max : int)
  requires s.Length > 0
  ensures forall k : int :: 0 <= k < s.Length ==> s [ k ] <= max
{
  var i := 0;
  max := s[0];
  while i < s.Length
    invariant 0 <= i <= s.Length
    invariant forall a : int :: 0 <= a < i ==> s [ a ] <= max
    decreases s.Length - i
  {
    if s [ i ] > max
    {
      max := s [ i ];
    }
    i := i + 1;
  }
}

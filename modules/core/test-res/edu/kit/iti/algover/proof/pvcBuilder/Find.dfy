method Find(a: array<int>, key: int) returns (index: int)
   requires a != null
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures forall k: int :: 0 <= k < a.Length ==> index < 0  ==> a[k] != key
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall k: int :: 0 <= k < index ==> a[k] != key
      decreases a.Length - index
   {
      if (a[index] == key)
      {
        return;
      }
      index := index + 1;
   }
   index := -1;
}

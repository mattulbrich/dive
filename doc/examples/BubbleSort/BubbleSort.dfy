function sorted(a:array<int>, low: int, high: int) : bool
requires a != null
requires 0 <= low <= high <= a.Length
//reads a;
{
forall j,k :: low <= j <k <high ==> a[j] <= a[k]
}

method BubbleSort(a: array<int>)
requires a != null && a.Length > 1;
modifies {a};
ensures sorted(a, 0, a.Length);
{
var sortedUntil := 0;
var i := a.Length - 1;
while(sortedUntil < a.Length)
invariant 0 <= sortedUntil <= a.Length;
invariant forall j, k :: 0 <= j < sortedUntil <= k < a.Length ==> a[j] <= a[k];
invariant sorted(a, 0, sortedUntil);
{
i := a.Length - 1;
while(i > sortedUntil)
invariant sortedUntil <= i < a.Length;
invariant forall j, k :: 0 <= j < sortedUntil <= k < a.Length ==> a[j] <= a[k];
invariant forall j :: i <= j < a.Length ==> a[i] <= a[j];
invariant sorted(a, 0, sortedUntil);
{
if(a[i] <= a[i - 1])
{
 a[i - 1] := a[i];
a[i] := a[i-1];
}
i := i - 1;
}
sortedUntil := sortedUntil + 1;
}
}

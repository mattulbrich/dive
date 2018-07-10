function sorted(a:array<int>, low: int, high: int) : bool
requires a != null
requires 0 <= low <= high <= a.Length
{
forall j,k :: low <= j <k <high ==> a[j] <= a[k]
}
method InsertionSort(a: array<int>)
requires a != null && a.Length > 1;
ensures sorted(a, 0, a.Length);
modifies {a};
{
var index := 1;
while(index < a.Length)
invariant 1 <= index <= a.Length;
invariant sorted(a, 0, index);
{
var counter := index - 1;
var temp := a[index];
a[index] := a[counter];
while(counter >= 0 && temp < a[counter])
invariant sorted(a, 0, index + 1);
invariant forall k :: counter < k < index ==> a[k] > temp;
{
a[counter + 1] := a[counter];
counter := counter - 1;
}
a[counter + 1] := temp;
index := index + 1;
}
}

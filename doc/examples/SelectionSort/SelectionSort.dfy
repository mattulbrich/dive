function sorted(a:array<int>, low: int, high: int) : bool
requires a != null
requires 0 <= low <= high <= a.Length
//reads a;
{
forall j,k :: low <= j <k <high ==> a[j] <= a[k]
}

method SelectionSort(a: array<int>)
 requires a != null && a.Length > 1;
 modifies {a};
 ensures sorted(a, 0, a.Length);
{
 var index := 0;
 var counter := 0;
 var minIndex := 0;
 while(index < a.Length)
 invariant 0 <= index <= a.Length;
 invariant sorted(a, 0, index);
 invariant forall j, k :: 0 <= j < index <= k < a.Length ==> a[j] <= a[k];
 {
minIndex := index;
counter := index;
while(counter < a.Length)
 invariant index <= counter <= a.Length;
 invariant index <= minIndex < a.Length;
 invariant forall k :: index <= k < counter ==> a[minIndex] <= a[k];
{
 if(a[minIndex] >= a[counter])
 {
 minIndex := counter;
 }
 counter := counter + 1;
}
a[minIndex] := a[index];
a[index] := a[minIndex];
index := index + 1;
 }
}

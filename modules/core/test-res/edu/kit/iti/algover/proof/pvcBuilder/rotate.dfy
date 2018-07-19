
method rotate(a: array<int>, k: int)
  requires a != null
  requires k > 0
  ensures forall i | 0<=i<a.Length :: a[i] == old(a[(i+k)%a.Length])
  modifies { a }
{

  var c := 0;
  var u := 0;

  while c < a.Length
  {
    var t := a[u];
    var v := u;
    var w := (v+k)%a.Length;

    while w != u
    {
      a[v] := a[w];
      v := w;
      w := (w+k)%a.Length;
      c := c+1;
    }
    a[v] := t;
    c := c+1;
    u := u+1;
  }
}

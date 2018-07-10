method folModel (i : int, j: int) returns (k: int)
requires i < 0
requires j > 0
ensures k < i
{
k := i - j;
}

method fol (a : bool, b: bool) returns (c: bool)
requires a
requires b
ensures c
{
c := a && b;
}
method fol2 (a : bool) returns (c: bool)
requires a
ensures a
{
}
method fol3 (a : bool, b: bool, c: bool) returns (d: bool)
ensures a ==> (b ==> a)
ensures (a && (a ==> b)) ==> b
ensures (a == b) == ((a == b) && (b ==> a))
ensures (a && (b || c)) == ((a && b) || (a && c))
ensures !(a || b) == (!a && !b)
{

}

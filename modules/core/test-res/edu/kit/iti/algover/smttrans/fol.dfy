method fol (a : bool, b: bool) returns (c: bool)
requires a
requires b
ensures c
{
c := a && b;
}

method fol2 (a : bool, b: bool, c: bool) returns (d: bool)
ensures a ==> (b ==> a)
ensures (a && (a ==> b)) ==> b
ensures (a && (b || c)) == ((a && b) || (a && c))
ensures !(a || b) == (!a && !b)
{

}

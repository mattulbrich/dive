// detected by S. Schwarz

class Actor {
var x : int;
}

method getNumber (a : Actor) returns (m :int)
ensures m >= 0
{
if (a.x > 0) {
m:= 0;
} else {
m:= 1;
}
}

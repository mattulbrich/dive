class Y {
    var y: int;
}
class X {
    var y: int;
}

method getNumber(o: X, p : Y)
    requires o != null
    ensures o.y > 5
    modifies {o,p}
{
    var x := o;
    o.y := 8;
}

method getNumber2(o: X, p : Y)
    requires o != null
    ensures o.y > 10
    modifies {o,p}
{
    var x := o;
    o.y := 8;
}

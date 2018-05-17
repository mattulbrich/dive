/*
 * Bug report #54 by Simon
 */
class X {
    var y: int;
}

method getNumber(o: X) 
    requires o != null
    ensures o.y > 5
    modifies { o }
{
    o.y := 8;
}


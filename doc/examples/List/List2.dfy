// RUN: %dafny /compile:0 /dprint:"%t.dprint" "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

class Node {
  ghost var List: seq<int>
  ghost var Repr: set<Node>

  var data: int
  var next: Node
/**
  function Valid() : bool
//    reads this, Repr
  {
    this in Repr &&
    (next == null ==> List == [data]) &&
    (next != null ==>
        next in Repr && next.Repr <= Repr &&
        !(this in next.Repr) &&
        List == [data] + next.List &&
        next.Valid())
  }

  method Init(d: int)
    ensures Valid() && fresh(Repr - {this})
    ensures List == [d]
    modifies this
  {
    data := d;
    next := null;
    List := [d];
    Repr := {this};
  }

  method InitAsPredecessor(d: int, succ: Node)
    requires succ != null
    requires succ.Valid()
    requires this !in succ.Repr
    ensures Valid() && fresh(Repr - {this} - succ.Repr)
    ensures List == [d] + succ.List
    modifies this
  {
    data := d;
    next := succ;
    Repr := {this} + succ.Repr;
    List := [d] + succ.List;
  }

  method Prepend(d: int) returns (r: Node)
    requires Valid()
    ensures r != null
    ensures r.Valid() && fresh(r.Repr - old(Repr))
    ensures r.List == [d] + List
  {
    r := new Node.InitAsPredecessor(d, this);
  }

  method Pop() returns (r: Node)
    requires Valid()
    ensures r == null ==> |List| == 1
    //ensures r != null ==> r.Valid() && r.List == List[1..] && r.Repr <= Repr
    ensures r != null ==> r.Valid()
    //ensures r.List == List[1..]
    ensures forall i :: 0 < i <= |r.List| ==> r.List[i-1] == List[i]
    ensures r.Repr <= this.Repr
  {
    r := next;
  }
**/
  method Get(index: int) returns (v: int)
    requires 0 <= index < |List|
  //  requires Valid()
    ensures v == List[index]
    decreases index
  {
    if (index == 0)
    {
      v := data;
    } else {
      v := next.Get(index - 1);
    }
  }

}

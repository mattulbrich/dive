class List {
  ghost var seqq: seq<int>;
  ghost var footprint: set<object>;

  var head: Node;
  
  function Valid() : bool
  {
    true
  }
  
  method size() returns (s: int)
    requires Valid()
    ensures s == |seqq|
  {
    assume false;
  }

  method insertAt(pos: int, value: int)
    requires 0 <= pos <= |seqq|
    ensures seqq == old(seqq[..pos] + [value] + seqq[pos..])
    modifies footprint
  {
    assume false;
  }

  method removeAt(pos: int)
    requires 0 <= pos < |seqq|
    ensures seqq == old(seqq[..pos] + seqq[pos+1..])
    modifies footprint
  {
    assume false;
  }

  method getAt(pos: int) returns (v: int)
    requires 0 <= pos < |seqq|
    ensures v == seqq[pos]
  {
    assume false;
  }
}



class Node {
  var value: int
  var next: Node
}

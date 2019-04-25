class Node {
  var value: int
  var next: Node

  method Init(value: int, next : Node) 
    modifies this;
  {
    this.value := value;
    this.next := next;
  }
}

class List {
  ghost var seqq: seq<int>;
  ghost var nodeseqq: seq<Node>;

  var head: Node;

  function Valid() : bool
  {
    |seqq| == |nodeseqq| &&
	(forall i :: i >= 0 && i < |seqq| ==> seqq[i] == nodeseqq[i].value) &&
	nodeseqq[0] == head &&
        nodeseqq[(|nodeseqq| - 1)].next == null &&
	(forall j :: j >= 0 && j < |nodeseqq| - 1 ==> nodeseqq[j].next == nodeseqq[j + 1]) &&
	(forall k :: k >= 0 && k < |nodeseqq| - 1 ==> nodeseqq[k].next != null) &&
	(forall n :: n >= 0 && n < |nodeseqq| ==> nodeseqq[n] != null) &&
	head != null
  }  
  
  method getAt(pos: int) returns (v: int)
    requires 0 <= pos < |seqq| && Valid()
    ensures v == seqq[pos]
  {
      var idx := 0;
      var node := head;
      while(idx < pos) 
        decreases |seqq| - idx;
	invariant label idxInv: idx >= 0 && idx <= pos;
	invariant label nodeInv: node == nodeseqq[idx];
      {
        node := node.next;
        idx := idx + 1;
      }
      v := node.value;
  }
}
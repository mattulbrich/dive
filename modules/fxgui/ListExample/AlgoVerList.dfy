
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
  ghost var footprint: set<object>;

  var head: Node;
  function Valid() : bool
  {
    |seqq| == |nodeseqq| &&
    |seqq| >= 1 &&
    head != null &&
    (forall n :: n >= 0 && n < |nodeseqq| ==> nodeseqq[n] != null) &&
    (forall i :: i >= 0 && i < |seqq| ==> seqq[i] == nodeseqq[i].value) &&
    (forall k :: k >= 0 && k < |nodeseqq| - 1 ==> nodeseqq[k].next != null) &&
    nodeseqq[0] == head &&
    nodeseqq[(|nodeseqq| - 1)].next == null &&
    (forall j :: j >= 0 && j < |nodeseqq| - 1 ==> nodeseqq[j].next == nodeseqq[j + 1]) 
  }   

  method size() returns (s: int)
    requires Valid()
    ensures s == |seqq|
  {
    s := 0;
    var node := head;
    while(node.next != null) 
      decreases |seqq| - s
      invariant node != null
      invariant s < |seqq| && s >= 0
      invariant node == nodeseqq[s]
    {
      node := node.next;
      s := s + 1;
    }
    s := s + 1;
  }
  
  //currently inserting at position 0 is not supported (but should be an easy extension)
  method insertAt(pos: int, value: int)
    requires 0 <= pos < |seqq| && Valid()
    ensures seqq == old(seqq[..pos] + [value] + seqq[pos..]) 
    ensures Valid()
    modifies footprint
  {
    var idx := 0;
    var node := head;
    while(idx < pos) 
      decreases |seqq| - idx;
      invariant idx <= pos && idx >= 0;
      invariant node == nodeseqq[idx];
    {
      node := node.next;
      idx := idx + 1;
    }
    var newNode := new Node;
    newNode.Init(value, node.next);
    node.next := newNode;
    nodeseqq := nodeseqq[..pos] + [newNode] + nodeseqq[pos..];
    seqq := seqq[..pos] + [value] + seqq[pos..];
  }
  
  method removeAt(pos: int)
    requires 0 <= pos < |seqq| &&  |seqq| >= 2 
    requires Valid()
    ensures seqq == old(seqq[..pos] + seqq[pos+1..])
    ensures Valid()
    modifies footprint
  {
    if(pos == 0) {      
        head := head.next;
    } else {
      var idx := 0;
      var node := head;
      while(idx < pos - 1) 
        decreases |seqq| - idx;
        invariant idx <= pos - 1 && idx >= 0;
        invariant node == nodeseqq[idx];
      {
        node := node.next;
        idx := idx + 1;
      }
      node.next := node.next.next;
    }
    nodeseqq := nodeseqq[..pos] + nodeseqq[pos + 1..];
    seqq := seqq[..pos] + seqq[pos + 1 ..];
  }
  
  method getAt(pos: int) returns (v: int)
    requires 0 <= pos < |seqq|
    requires Valid()
    ensures v == seqq[pos]
  {
    var idx := 0;
      var node := head;
      while(idx < pos) 
	invariant node == nodeseqq[idx];
	invariant idx <= pos;
        decreases |seqq| - idx;
      {
        node := node.next;
        idx := idx + 1;
      }
      v := node.value;
  }
}

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
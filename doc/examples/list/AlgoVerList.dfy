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
    s := 0;
    var node := head;
    while(node != null) 
      decreases |seqq| - s
    {
      node := node.next;
      s := s + 1;
    }
  }
  
  method insertAt(pos: int, value: int)
    requires 0 <= pos <= |seqq| && Valid()
    ensures seqq == old(seqq[..pos] + [value] + seqq[pos..])
    modifies footprint
  {
    var idx := 0;
    var node := head;
    while(idx < pos) 
      decreases |seqq| - idx;
    {
      node := node.next;
      idx := idx + 1;
    }
    var newNode := new Node;
    node.next := new Node.Init(value, node.next);
    seqq := seqq[..pos] + [value] + seqq[pos..];
  }
  
  method removeAt(pos: int)
    requires 0 <= pos < |seqq|
    ensures seqq == old(seqq[..pos] + seqq[pos+1..])
    modifies footprint
  {
    if(pos == 0) {
      if(head.next == null) {
        head := null;
      } else {
        head := head.next;
      }
    } else {
      var idx := 0;
      var node := head;
      while(idx < pos) 
        decreases |seqq| - idx;
      {
        node := node.next;
        idx := idx + 1;
      }
      if(node.next == null) {
        node.next := null;
      } else {
        node.next := node.next.next;
      }
    }
    seqq := seqq[..pos] + seqq[pos+1..];
  }
  
  method getAt(pos: int) returns (v: int)
    requires 0 <= pos < |seqq|
    ensures v == seqq[pos]
  {
    var idx := 0;
      var node := head;
      while(idx < pos) 
        decreases |seqq| - idx;
      {
        node := node.next;
        idx := idx + 1;
      }
      v := node.value;
  }
  
}
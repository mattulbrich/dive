class Node
{
  var next : Node?;
  var value : int;
  ghost var depth : int;
  ghost var footprint : set<object>;

  function Valid() : bool
    reads this, footprint
    decreases depth
  {
    this in footprint &&
      this.depth >= 0 &&
      (this.next != null ==>
        next in footprint && next.footprint <= footprint &&
        next.depth < depth && next.Valid())
  }
}

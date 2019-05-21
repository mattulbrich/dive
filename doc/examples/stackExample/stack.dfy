//\\ settings { "Sequent Generation Type" = "ssa" }

class BoundedStack {
	var data : seq<int>;
	var curSize : int;
	var maxSize : int;

	function valid() : bool
	{
		this.curSize >= 0 && this.curSize <= |this.data| &&
		this.maxSize >= this.curSize && this.maxSize == |this.data|
	}
	
	method pop() returns (res : int)
		requires this.curSize > 0 && valid();
		ensures this.curSize == old(this.curSize - 1) && valid() && res == this.data[this.curSize];
	{
		res := this.data[this.curSize -1];
		this.curSize := this.curSize - 1;	
	}

	method push(n : int) 
		requires this.curSize < this.maxSize && valid();
		ensures this.data[this.curSize - 1] == n;
		ensures this.curSize == old(this.curSize) + 1 && valid();
	{
		this.data[this.curSize] := n;		
		this.curSize := this.curSize + 1;
	}
}

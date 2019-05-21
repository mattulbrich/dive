class BoundedStack {
	var data : seq<int>;
	var curSize : int;
	var maxSize : int;

	function valid() : bool
	{
		curSize >= 0 && curSize <= |data| &&
		maxSize >= curSize && maxSize == |data|
	}
	
	method pop() returns (res : int)
		requires curSize > 0 && valid();
		ensures curSize == old(curSize - 1) && valid() && res == data[curSize];
	{
		var res : int;
		res := data[curSize -1];
		curSize := curSize - 1;	
	}

	method push(n : int) 
		requires curSize < maxSize && valid();
		ensures data[curSize - 1] == n;
		ensures curSize == old(curSize) + 1 && valid();
	{
		data[curSize] := n;		
		curSize := curSize + 1;
	}
}
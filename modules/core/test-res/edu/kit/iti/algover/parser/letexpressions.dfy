// testing let expressions

method f()
{
	var i:int := let x := 5; x+1;

	var j:int := let x,y := i,i+1; x+y;

	// This seems to be allowed in Dafny, but cannot yet ...
	// if (3 + let i,j:=j,i; i-j) == 0
	// {}


	if 3 + (let i,j:=j,i; i-j) == 0
	{}

	var o:object := let i:=null; i;
}